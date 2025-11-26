// Модуль для мониторинга свойств живости (Liveness) в runtime

use std::collections::HashMap;
use std::time::{Duration, Instant};
use sysinfo::Pid;

/// Мониторинг свойств живости
pub struct LivenessMonitor {
    /// Время последней реакции на перегрузку
    last_adjustment_time: Option<Instant>,
    /// Счетчик корректировок для каждого процесса
    adjustment_counts: HashMap<Pid, usize>,
    /// Время обнаружения перегрузки
    overload_detected_at: Option<Instant>,
    /// Максимальное время реакции (из конфигурации)
    max_response_time: Duration,
}

impl LivenessMonitor {
    pub fn new(max_response_time_ms: u64) -> Self {
        Self {
            last_adjustment_time: None,
            adjustment_counts: HashMap::new(),
            overload_detected_at: None,
            max_response_time: Duration::from_millis(max_response_time_ms),
        }
    }

    /// L1: Конечная корректировка при перегрузке
    /// Формально: (load > threshold) ⇝ ∃p: priority(p) = MIN_PRIORITY
    pub fn check_eventual_adjustment(
        &mut self,
        is_overloaded: bool,
        has_min_priority_process: bool,
    ) -> bool {
        if is_overloaded {
            if self.overload_detected_at.is_none() {
                self.overload_detected_at = Some(Instant::now());
                log::info!("[Liveness] Overload detected, starting timer");
            }

            if has_min_priority_process {
                if let Some(detected_at) = self.overload_detected_at {
                    let response_time = detected_at.elapsed();
                    log::info!(
                        "[Liveness] ✓ L1: Eventual adjustment satisfied in {:?}",
                        response_time
                    );
                    self.overload_detected_at = None;
                    return true;
                }
            } else if let Some(detected_at) = self.overload_detected_at {
                let elapsed = detected_at.elapsed();
                if elapsed > self.max_response_time {
                    log::warn!(
                        "[Liveness] ✗ L1: No adjustment after {:?} (max: {:?})",
                        elapsed,
                        self.max_response_time
                    );
                    return false;
                }
            }
        } else {
            self.overload_detected_at = None;
        }
        true
    }

    /// L2: Очистка завершенных процессов
    /// Формально: ∀p: terminated(p) ⇝ ¬monitored(p)
    pub fn check_cleanup(&self, terminated_pids: &[Pid], still_monitored: &[Pid]) -> bool {
        for pid in terminated_pids {
            if still_monitored.contains(pid) {
                log::warn!(
                    "[Liveness] ✗ L2: Terminated process {} still monitored",
                    pid
                );
                return false;
            }
        }
        log::debug!("[Liveness] ✓ L2: All terminated processes cleaned up");
        true
    }

    /// L3: Отсутствие застревания в перегрузке
    /// Формально: □◇(load ≤ NUM_CPUS × CRITICAL_MULT)
    pub fn check_no_permanent_overload(
        &mut self,
        is_overloaded: bool,
        max_overload_duration: Duration,
    ) -> bool {
        if is_overloaded {
            if self.overload_detected_at.is_none() {
                self.overload_detected_at = Some(Instant::now());
            } else if let Some(detected_at) = self.overload_detected_at {
                let duration = detected_at.elapsed();
                if duration > max_overload_duration {
                    log::error!(
                        "[Liveness] ✗ L3: System stuck in overload for {:?}",
                        duration
                    );
                    return false;
                }
            }
        } else {
            if self.overload_detected_at.is_some() {
                log::info!("[Liveness] ✓ L3: System recovered from overload");
                self.overload_detected_at = None;
            }
        }
        true
    }

    /// L4: Обнаружение новых процессов
    /// Формально: ∀p: matches(p) ⇝ monitored(p)
    pub fn check_process_discovery(&self, matching_pids: &[Pid], monitored_pids: &[Pid]) -> bool {
        for pid in matching_pids {
            if !monitored_pids.contains(pid) {
                log::warn!(
                    "[Liveness] ✗ L4: Matching process {} not yet monitored",
                    pid
                );
                return false;
            }
        }
        log::debug!("[Liveness] ✓ L4: All matching processes monitored");
        true
    }

    /// Регистрация корректировки приоритета
    pub fn record_adjustment(&mut self, pid: Pid) {
        *self.adjustment_counts.entry(pid).or_insert(0) += 1;
        self.last_adjustment_time = Some(Instant::now());
        log::debug!("[Liveness] Recorded adjustment for PID {}", pid);
    }

    /// P1: Ограниченность корректировок
    /// Формально: ∀p: adjustments(p) ≤ ⌈(MAX_PRIORITY - MIN_PRIORITY) / min_step⌉
    pub fn check_bounded_adjustments(&self, pid: Pid, max_adjustments: usize) -> bool {
        if let Some(&count) = self.adjustment_counts.get(&pid) {
            if count > max_adjustments {
                log::error!(
                    "[Liveness] ✗ P1: Process {} exceeded max adjustments: {} > {}",
                    pid,
                    count,
                    max_adjustments
                );
                return false;
            }
        }
        true
    }

    /// Очистка данных для завершенного процесса
    pub fn cleanup_process(&mut self, pid: Pid) {
        self.adjustment_counts.remove(&pid);
    }

    /// Получить статистику
    pub fn get_stats(&self) -> LivenessStats {
        LivenessStats {
            total_processes: self.adjustment_counts.len(),
            total_adjustments: self.adjustment_counts.values().sum(),
            overload_duration: self.overload_detected_at.map(|t| t.elapsed()),
        }
    }
}

#[derive(Debug)]
pub struct LivenessStats {
    pub total_processes: usize,
    pub total_adjustments: usize,
    pub overload_duration: Option<Duration>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eventual_adjustment() {
        let mut monitor = LivenessMonitor::new(5000);

        // Обнаружение перегрузки
        assert!(monitor.check_eventual_adjustment(true, false));

        // Реакция на перегрузку
        assert!(monitor.check_eventual_adjustment(true, true));
    }

    #[test]
    fn test_cleanup() {
        let monitor = LivenessMonitor::new(5000);
        let terminated = vec![Pid::from(123)];
        let monitored = vec![Pid::from(456)];

        assert!(monitor.check_cleanup(&terminated, &monitored));
    }

    #[test]
    fn test_bounded_adjustments() {
        let mut monitor = LivenessMonitor::new(5000);
        let pid = Pid::from(123);

        for _ in 0..5 {
            monitor.record_adjustment(pid);
        }

        assert!(monitor.check_bounded_adjustments(pid, 10));
        assert!(!monitor.check_bounded_adjustments(pid, 3));
    }
}
