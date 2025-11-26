// Сломанные версии функций - демонстрация того, что может пойти не так!

pub const MIN_PRIORITY: i32 = 10;
pub const MAX_PRIORITY: i32 = 95;

/// ❌ СЛОМАННАЯ ВЕРСИЯ 1: Нет проверки границ
pub fn calculate_priority_broken_v1(
    target_priority: i32,
    load: f64,
    responsiveness_ms: u64,
    available_memory_mb: u64,
    num_cpus: usize,
) -> i32 {
    let mut priority = target_priority;

    if load > (num_cpus as f64) * 2.0 {
        priority = priority - 10;  // ❌ Может уйти в отрицательные!
    }

    if responsiveness_ms > 2000 {
        priority = priority - 5;   // ❌ Может уйти в отрицательные!
    }

    if available_memory_mb < 100 {
        priority = priority - 3;   // ❌ Может уйти в отрицательные!
    }

    priority  // ❌ Нет clamp!
}

/// ❌ СЛОМАННАЯ ВЕРСИЯ 2: Overflow при вычитании
pub fn apply_adjustment_broken_v2(old_priority: i32, step: i32) -> i32 {
    old_priority - step  // ❌ Может вызвать overflow!
}

/// ❌ СЛОМАННАЯ ВЕРСИЯ 3: Деление на ноль
pub fn calculate_priority_broken_v3(
    target_priority: i32,
    load: f64,
    num_cpus: usize,
) -> i32 {
    let threshold = (num_cpus as f64) * 2.0;  // ❌ Если num_cpus = 0, threshold = 0
    
    if load > threshold {
        let adjustment = (load / threshold) as i32;  // ❌ Деление на ноль!
        return target_priority - adjustment;
    }
    
    target_priority
}

/// ❌ СЛОМАННАЯ ВЕРСИЯ 4: Бесконечный цикл
pub fn adjust_until_min_broken_v4(mut priority: i32, step: i32) -> i32 {
    while priority > MIN_PRIORITY {
        priority = priority - step;  // ❌ Может уйти ниже MIN и зациклиться!
    }
    priority
}

/// ❌ СЛОМАННАЯ ВЕРСИЯ 5: Неправильная логика
pub fn calculate_priority_broken_v5(
    target_priority: i32,
    load: f64,
    num_cpus: usize,
) -> i32 {
    if load > (num_cpus as f64) * 2.0 {
        return target_priority + 10;  // ❌ УВЕЛИЧИВАЕТ вместо уменьшения!
    }
    target_priority
}

#[cfg(test)]
mod broken_tests {
    use super::*;

    // 🔨 Демонстрация: Сломанная версия 1
    #[test]
    #[should_panic]
    fn test_broken_v1_negative() {
        let result = calculate_priority_broken_v1(20, 1000.0, 10000, 0, 1);
        assert!(result >= MIN_PRIORITY, "FAIL: result = {}", result);
    }

    // 🔨 Демонстрация: Сломанная версия 2
    #[test]
    #[should_panic]
    fn test_broken_v2_overflow() {
        let result = apply_adjustment_broken_v2(MIN_PRIORITY, i32::MAX);
        assert!(result >= MIN_PRIORITY, "FAIL: overflow, result = {}", result);
    }

    // 🔨 Демонстрация: Сломанная версия 3
    #[test]
    #[should_panic]
    fn test_broken_v3_division_by_zero() {
        let result = calculate_priority_broken_v3(50, 100.0, 0);
        assert!(result >= MIN_PRIORITY, "FAIL: division by zero");
    }

    // 🔨 Демонстрация: Сломанная версия 4
    #[test]
    #[should_panic]
    fn test_broken_v4_infinite_loop() {
        // С отрицательным шагом цикл продолжается и происходит overflow
        // В release mode wrapping приводит к i32::MIN
        let result = adjust_until_min_broken_v4(95, -1);  // ❌ Отрицательный шаг!
        assert_eq!(result, MIN_PRIORITY, "FAIL: overflow, result = {}", result);
    }

    // 🔨 Демонстрация: Сломанная версия 5
    #[test]
    #[should_panic]
    fn test_broken_v5_wrong_logic() {
        let result = calculate_priority_broken_v5(90, 1000.0, 1);
        assert!(result <= 90, "FAIL: priority increased! result = {}", result);
    }
}
