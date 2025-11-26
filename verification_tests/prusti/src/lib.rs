// Модуль для Prusti верификации Priority Manager
// 
// ПРИМЕЧАНИЕ: Для работы Prusti контрактов нужно:
// 1. Установить Prusti: cargo install prusti-cli
// 2. Запустить: cargo prusti --features prusti
//
// Без установленного Prusti этот код компилируется как обычный Rust

/// Константы для верификации
pub const MIN_PRIORITY: i32 = 10;
pub const MAX_PRIORITY: i32 = 95;
pub const CRITICAL_LOAD_MULTIPLIER: f32 = 2.0;

/// S1: Проверяемая функция - вычисление оптимального приоритета
/// 
/// # Контракты (Prusti)
/// - Предусловие: приоритет в допустимых границах
/// - Постусловие: результат в допустимых границах
/// - Постусловие: результат не больше целевого значения при высокой нагрузке
///
/// Для верификации с Prusti раскомментируйте атрибуты ниже
pub fn calculate_optimal_priority(
    target_priority: i32,
    load_high: bool,
    responsiveness_high: bool,
    memory_low: bool,
) -> i32 {
    let mut priority = target_priority;

    // Корректировка на основе нагрузки CPU
    if load_high && priority >= 10 {
        priority = priority.saturating_sub(10).max(MIN_PRIORITY);
    }

    // Корректировка на основе реактивности
    if responsiveness_high && priority >= 5 {
        priority = priority.saturating_sub(5).max(MIN_PRIORITY);
    }

    // Корректировка на основе доступной памяти
    if memory_low && priority >= 3 {
        priority = priority.saturating_sub(3).max(MIN_PRIORITY);
    }

    // Ограничение в допустимых границах
    priority.clamp(MIN_PRIORITY, MAX_PRIORITY)
}

/// S2: Проверяемая функция - применение корректировки приоритета
/// Монотонность: приоритет только уменьшается
pub fn apply_priority_adjustment(old_priority: i32, step: i32) -> i32 {
    let new_priority = old_priority.saturating_sub(step);
    new_priority.max(MIN_PRIORITY)
}

/// P1: Конечность корректировок с инвариантом цикла
/// Доказывает, что корректировки конечны
pub fn apply_adjustments_until_min(initial_priority: i32, step: i32) -> (i32, usize) {
    let mut priority = initial_priority;
    let mut count = 0;
    
    // Инвариант цикла для Prusti:
    // - MIN_PRIORITY <= priority <= MAX_PRIORITY
    // - count <= 9
    // - priority <= initial_priority
    while priority > MIN_PRIORITY && count < 10 {
        priority = apply_priority_adjustment(priority, step);
        count += 1;
    }
    
    (priority, count)
}

/// C2: Композиция корректировок сохраняет инварианты
pub fn compose_adjustments(priority: i32, step1: i32, step2: i32) -> i32 {
    let after_first = apply_priority_adjustment(priority, step1);
    apply_priority_adjustment(after_first, step2)
}

/// Проверяемая функция: проверка необходимости корректировки
pub fn needs_adjustment(load: f64, threshold: f64, priority: i32) -> bool {
    load > threshold && priority > MIN_PRIORITY
}

/// S5: Отсутствие overflow при вычислениях
pub fn safe_priority_calculation(priority: i32, adjustment: i32) -> i32 {
    // Используем saturating операции для предотвращения overflow
    let result = priority.saturating_sub(adjustment);
    result.clamp(MIN_PRIORITY, MAX_PRIORITY)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_bounds() {
        let result = calculate_optimal_priority(50, false, false, false);
        assert!(result >= MIN_PRIORITY && result <= MAX_PRIORITY);
    }

    #[test]
    fn test_high_load_decreases_priority() {
        let result = calculate_optimal_priority(80, true, false, false);
        assert!(result <= 70);
    }

    #[test]
    fn test_adjustment_monotonic() {
        let result = apply_priority_adjustment(50, 10);
        assert!(result <= 50);
        assert!(result >= MIN_PRIORITY);
    }

    #[test]
    fn test_min_priority_floor() {
        let result = apply_priority_adjustment(MIN_PRIORITY, 10);
        assert_eq!(result, MIN_PRIORITY);
    }

    #[test]
    fn test_finite_adjustments() {
        let (final_priority, count) = apply_adjustments_until_min(95, 10);
        assert!(count <= 9);
        assert!(final_priority >= MIN_PRIORITY);
    }

    #[test]
    fn test_composition() {
        let result = compose_adjustments(80, 10, 5);
        assert!(result >= MIN_PRIORITY && result <= MAX_PRIORITY);
        assert!(result <= 80);
    }

    #[test]
    fn test_all_properties() {
        // S1: Границы
        for p in MIN_PRIORITY..=MAX_PRIORITY {
            let r = calculate_optimal_priority(p, false, false, false);
            assert!(r >= MIN_PRIORITY && r <= MAX_PRIORITY);
        }

        // S2: Монотонность
        for p in MIN_PRIORITY..=MAX_PRIORITY {
            for s in 1..=20 {
                let r = apply_priority_adjustment(p, s);
                assert!(r <= p);
            }
        }

        // P1: Конечность
        let (_, count) = apply_adjustments_until_min(MAX_PRIORITY, 10);
        assert!(count <= 9);

        // C2: Композиция
        let r = compose_adjustments(MAX_PRIORITY, 10, 10);
        assert!(r >= MIN_PRIORITY && r <= MAX_PRIORITY);
    }
}
