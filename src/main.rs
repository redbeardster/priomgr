use clap::{Arg, Command};
use nix::unistd::Pid as NixPid;
use num_cpus;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use sysinfo::{
    CpuRefreshKind, Pid, PidExt, ProcessExt, ProcessRefreshKind, RefreshKind, System, SystemExt,
};
use tokio::sync::RwLock;

mod liveness_monitor;
mod verification;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProcessConfig {
    name_pattern: String,
    target_priority: i32,
    policy: String,
    auto_adjust: bool,
    max_priority: Option<i32>,
    min_priority: Option<i32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SystemConfig {
    check_interval_ms: u64,
    max_rt_priority: i32,
    min_rt_priority: i32,
    responsiveness_threshold_ms: u64,
    critical_load_multiplier: f32,
    monitored_processes: Vec<ProcessConfig>,
}

#[derive(Debug, Clone)]
struct MonitoredProcess {
    pid: Pid,
    #[allow(dead_code)]
    name: String,
    config: ProcessConfig,
    current_priority: i32,
    last_adjustment: Instant,
}

struct SystemHealth {
    load_average: f64,
    available_memory: u64,
    responsiveness: Duration,
    #[allow(dead_code)]
    stalled_tasks: usize,
}

struct PriorityManager {
    config: SystemConfig,
    monitored: Arc<RwLock<HashMap<Pid, MonitoredProcess>>>,
    system: System,
    liveness_monitor: liveness_monitor::LivenessMonitor,
}

impl PriorityManager {
    fn new(config: SystemConfig) -> Self {
        let max_response_time = config.check_interval_ms * 10; // 10 циклов
        Self {
            config,
            monitored: Arc::new(RwLock::new(HashMap::new())),
            system: System::new_with_specifics(
                RefreshKind::new()
                    .with_memory()
                    .with_cpu(CpuRefreshKind::everything())
                    .with_processes(ProcessRefreshKind::everything()),
            ),
            liveness_monitor: liveness_monitor::LivenessMonitor::new(max_response_time),
        }
    }

    async fn discover_processes(&mut self) {
        self.system.refresh_processes();

        for (pid, process) in self.system.processes() {
            for process_config in &self.config.monitored_processes {
                if process.name().contains(&process_config.name_pattern) {
                    let mut monitored = self.monitored.write().await;

                    if !monitored.contains_key(pid) {
                        let monitored_process = MonitoredProcess {
                            pid: *pid,
                            name: process.name().to_string(),
                            config: process_config.clone(),
                            current_priority: 0,
                            last_adjustment: Instant::now(),
                        };

                        log::info!("Discovered new process: {} (PID: {})", process.name(), pid);

                        monitored.insert(*pid, monitored_process);
                        if let Err(e) = self.apply_priority(*pid, process_config).await {
                            log::error!("Failed to apply initial priority: {}", e);
                        }
                    }
                }
            }
        }
    }

    async fn apply_priority(&self, pid: Pid, config: &ProcessConfig) -> Result<(), String> {
        let nix_pid = NixPid::from_raw(pid.as_u32() as i32);

        // В новых версиях nix API для планировщика изменился
        // Используем libc напрямую для установки приоритета
        let policy = match config.policy.as_str() {
            "fifo" => libc::SCHED_FIFO,
            "rr" => libc::SCHED_RR,
            "other" => libc::SCHED_OTHER,
            _ => return Err(format!("Unknown policy: {}", config.policy)),
        };

        let param = libc::sched_param {
            sched_priority: config.target_priority,
        };

        let result = unsafe { libc::sched_setscheduler(nix_pid.as_raw(), policy, &param) };

        if result == 0 {
            log::info!(
                "Set priority {} for PID {} ({})",
                config.target_priority,
                pid,
                config.name_pattern
            );
            Ok(())
        } else {
            let error = std::io::Error::last_os_error();
            log::error!("Failed to set priority for PID {}: {}", pid, error);
            Err(format!("Failed to set priority: {}", error))
        }
    }

    async fn check_system_health(&mut self) -> SystemHealth {
        self.system.refresh_memory();
        let load_avg = self.system.load_average();
        let memory = self.system.available_memory();

        // Проверка реактивности системы
        let responsiveness = self.measure_responsiveness().await;

        SystemHealth {
            load_average: load_avg.one,
            available_memory: memory,
            responsiveness,
            stalled_tasks: 0,
        }
    }

    async fn measure_responsiveness(&self) -> Duration {
        let start = Instant::now();

        // Простая проверка - системный вызов
        let _ = std::fs::metadata("/");

        start.elapsed()
    }

    async fn adjust_priorities_based_on_health(&mut self, health: &SystemHealth) {
        let mut monitored = self.monitored.write().await;

        for monitored_process in monitored.values_mut() {
            if !monitored_process.config.auto_adjust {
                continue;
            }

            let new_priority = self.calculate_optimal_priority(monitored_process, health);

            if new_priority != monitored_process.current_priority {
                if let Err(e) = self
                    .set_process_priority(
                        monitored_process.pid,
                        new_priority,
                        &monitored_process.config.policy,
                    )
                    .await
                {
                    log::error!(
                        "Failed to adjust priority for PID {}: {}",
                        monitored_process.pid,
                        e
                    );
                } else {
                    monitored_process.current_priority = new_priority;
                    monitored_process.last_adjustment = Instant::now();

                    // Регистрируем корректировку для мониторинга живости
                    self.liveness_monitor
                        .record_adjustment(monitored_process.pid);

                    log::info!(
                        "Adjusted priority for PID {} to {} (load: {:.2})",
                        monitored_process.pid,
                        new_priority,
                        health.load_average
                    );
                }
            }
        }
    }

    fn calculate_optimal_priority(&self, process: &MonitoredProcess, health: &SystemHealth) -> i32 {
        let mut priority = process.config.target_priority;

        // Корректировка на основе нагрузки системы
        if health.load_average
            > (num_cpus::get() as f64) * self.config.critical_load_multiplier as f64
        {
            priority = (priority - 10).max(self.config.min_rt_priority);
            log::warn!(
                "High system load ({:.2}), reducing priorities",
                health.load_average
            );
        }

        // Корректировка на основе реактивности
        if health.responsiveness > Duration::from_millis(self.config.responsiveness_threshold_ms) {
            priority = (priority - 5).max(self.config.min_rt_priority);
            log::warn!(
                "Poor system responsiveness ({:?}), reducing priorities",
                health.responsiveness
            );
        }

        // Корректировка на основе доступной памяти
        if health.available_memory < 100 * 1024 * 1024 {
            // < 100MB
            priority = (priority - 3).max(self.config.min_rt_priority);
        }

        priority.clamp(
            process
                .config
                .min_priority
                .unwrap_or(self.config.min_rt_priority),
            process
                .config
                .max_priority
                .unwrap_or(self.config.max_rt_priority),
        )
    }

    async fn set_process_priority(
        &self,
        pid: Pid,
        priority: i32,
        policy: &str,
    ) -> Result<(), String> {
        let nix_pid = NixPid::from_raw(pid.as_u32() as i32);

        let sched_policy = match policy {
            "fifo" => libc::SCHED_FIFO,
            "rr" => libc::SCHED_RR,
            _ => libc::SCHED_OTHER,
        };

        let param = libc::sched_param {
            sched_priority: priority,
        };

        let result = unsafe { libc::sched_setscheduler(nix_pid.as_raw(), sched_policy, &param) };

        if result == 0 {
            Ok(())
        } else {
            let error = std::io::Error::last_os_error();
            Err(format!("Failed to set scheduler: {}", error))
        }
    }

    async fn run_monitoring_loop(mut self) {
        log::info!(
            "Priority Manager started with {} CPU cores",
            num_cpus::get()
        );
        log::info!("Liveness monitoring enabled");

        let mut cycle_count = 0;
        let max_overload_duration = Duration::from_secs(60); // 1 минута максимум

        loop {
            // Обнаружение новых процессов
            self.discover_processes().await;

            // Проверка здоровья системы
            let health = self.check_system_health().await;

            let is_overloaded = health.responsiveness
                > Duration::from_millis(self.config.responsiveness_threshold_ms)
                || health.load_average
                    > (num_cpus::get() as f64) * self.config.critical_load_multiplier as f64;

            // Логирование состояния (только при проблемах или раз в 10 циклов)
            cycle_count += 1;
            if cycle_count % 10 == 0 || is_overloaded {
                log::info!(
                    "System health - Load: {:.2}, Memory: {} MB, Responsiveness: {:?}",
                    health.load_average,
                    health.available_memory / 1024 / 1024,
                    health.responsiveness
                );

                let stats = self.liveness_monitor.get_stats();
                log::info!(
                    "Liveness stats - Processes: {}, Adjustments: {}, Overload: {:?}",
                    stats.total_processes,
                    stats.total_adjustments,
                    stats.overload_duration
                );
            }

            // Корректировка приоритетов при необходимости
            if is_overloaded {
                self.adjust_priorities_based_on_health(&health).await;
            }

            // Проверка свойств живости
            let monitored = self.monitored.read().await;
            let has_min_priority = monitored
                .values()
                .any(|p| p.current_priority == self.config.min_rt_priority);
            drop(monitored);

            // L1: Конечная корректировка при перегрузке
            self.liveness_monitor
                .check_eventual_adjustment(is_overloaded, has_min_priority);

            // L3: Отсутствие застревания в перегрузке
            self.liveness_monitor
                .check_no_permanent_overload(is_overloaded, max_overload_duration);

            // Очистка завершенных процессов
            self.cleanup_finished_processes().await;

            tokio::time::sleep(Duration::from_millis(self.config.check_interval_ms)).await;
        }
    }

    async fn cleanup_finished_processes(&mut self) {
        let mut monitored = self.monitored.write().await;
        let before_count = monitored.len();

        // Обновляем информацию о процессах
        self.system.refresh_processes();

        let mut terminated_pids = Vec::new();
        monitored.retain(|&pid, _| {
            self.system.refresh_process(pid);
            let is_alive = self.system.process(pid).is_some();
            if !is_alive {
                terminated_pids.push(pid);
            }
            is_alive
        });

        // Проверяем свойство L2: очистка завершенных процессов
        let still_monitored: Vec<Pid> = monitored.keys().copied().collect();
        self.liveness_monitor
            .check_cleanup(&terminated_pids, &still_monitored);

        // Очищаем данные мониторинга для завершенных процессов
        for pid in terminated_pids {
            self.liveness_monitor.cleanup_process(pid);
        }

        let after_count = monitored.len();
        if before_count != after_count {
            log::info!(
                "Cleaned up {} finished processes",
                before_count - after_count
            );
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let matches = Command::new("Priority Manager")
        .version("1.0")
        .author("System Admin")
        .about("Manages process priorities dynamically")
        .arg(
            Arg::new("config")
                .short('c')
                .long("config")
                .value_name("FILE")
                .help("Sets a custom config file")
                .default_value("/etc/priority-manager/config.toml"),
        )
        .arg(
            Arg::new("daemon")
                .short('d')
                .long("daemon")
                .help("Run as daemon"),
        )
        .get_matches();

    let config_path = matches.get_one::<String>("config").unwrap();

    // Загрузка конфигурации
    let config_content = match std::fs::read_to_string(config_path) {
        Ok(content) => content,
        Err(e) => {
            log::error!("Failed to read config file {}: {}", config_path, e);
            // Создаем базовую конфигурацию
            let default_config = SystemConfig {
                check_interval_ms: 5000,
                max_rt_priority: 95,
                min_rt_priority: 10,
                responsiveness_threshold_ms: 2000,
                critical_load_multiplier: 2.0,
                monitored_processes: vec![
                    ProcessConfig {
                        name_pattern: "ffmpeg".to_string(),
                        target_priority: 85,
                        policy: "fifo".to_string(),
                        auto_adjust: true,
                        max_priority: Some(90),
                        min_priority: Some(50),
                    },
                    ProcessConfig {
                        name_pattern: "audio".to_string(),
                        target_priority: 80,
                        policy: "rr".to_string(),
                        auto_adjust: true,
                        max_priority: Some(85),
                        min_priority: Some(40),
                    },
                ],
            };

            // Сохраняем default config
            if let Some(parent) = std::path::Path::new(config_path).parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(config_path, toml::to_string_pretty(&default_config)?)?;
            log::info!("Created default configuration at {}", config_path);

            toml::to_string_pretty(&default_config)?
        }
    };

    let config: SystemConfig = toml::from_str(&config_content)?;

    log::info!(
        "Starting Priority Manager service with {} monitored process patterns",
        config.monitored_processes.len()
    );

    let manager = PriorityManager::new(config);
    manager.run_monitoring_loop().await;

    Ok(())
}
