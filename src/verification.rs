// Модуль с контрактами и верификацией для Prusti и Kani

// use crate::*;  // Не нужно для standalone проверки

/// Константы для верификации
pub const MIN_PRIORITY: i32 = 10;
pub const MAX_PRIORITY: i32 = 95;
pub const CRITICAL_LOAD_MULTIPLIER: f32 = 2.0;

/// Проверяемая функция: вычисление оптимального приоритета
///
/// # Контракты (Prusti)
/// - Предусловие: приоритет в допустимых границах
/// - Постусловие: результат в допустимых границах
/// - Постусловие: результат не больше целевого значения при высокой нагрузке
#[cfg_attr(feature = "prusti", requires(MIN_PRIORITY <= target_priority && target_priority <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(MIN_PRIORITY <= result && result <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(load > 50.0 ==> result <= target_priority))]
pub fn calculate_optimal_priority_verified(
    _current_priority: i32, // Не используется, но оставлен для совместимости
    target_priority: i32,
    load: f64,
    responsiveness_ms: u64,
    available_memory_mb: u64,
    num_cpus: usize,
) -> i32 {
    let mut priority = target_priority;

    // Корректировка на основе нагрузки CPU
    if load > (num_cpus as f64) * CRITICAL_LOAD_MULTIPLIER as f64 {
        priority = (priority - 10).max(MIN_PRIORITY);
    }

    // Корректировка на основе реактивности
    if responsiveness_ms > 2000 {
        priority = (priority - 5).max(MIN_PRIORITY);
    }

    // Корректировка на основе доступной памяти
    if available_memory_mb < 100 {
        priority = (priority - 3).max(MIN_PRIORITY);
    }

    // Ограничение в допустимых границах
    priority.clamp(MIN_PRIORITY, MAX_PRIORITY)
}

/// Проверяемая функция: применение корректировки приоритета
#[cfg_attr(feature = "prusti", requires(MIN_PRIORITY <= old_priority && old_priority <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", requires(step > 0))]
#[cfg_attr(feature = "prusti", ensures(MIN_PRIORITY <= result && result <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(result <= old_priority))]
pub fn apply_priority_adjustment(old_priority: i32, step: i32) -> i32 {
    (old_priority - step).max(MIN_PRIORITY)
}

/// Проверяемая функция: проверка необходимости корректировки
#[cfg_attr(feature = "prusti", pure)]
pub fn needs_adjustment(load: f64, threshold: f64, priority: i32) -> bool {
    load > threshold && priority > MIN_PRIORITY
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Kani proof: приоритет всегда в границах
    #[kani::proof]
    fn verify_priority_bounds() {
        let current_priority: i32 = kani::any();
        let target_priority: i32 = kani::any();
        let load: f64 = kani::any();
        let responsiveness: u64 = kani::any();
        let memory: u64 = kani::any();
        let cpus: usize = kani::any();

        // Предусловия
        kani::assume(MIN_PRIORITY <= current_priority && current_priority <= MAX_PRIORITY);
        kani::assume(MIN_PRIORITY <= target_priority && target_priority <= MAX_PRIORITY);
        kani::assume(load >= 0.0 && load <= 100.0);
        kani::assume(responsiveness <= 10000);
        kani::assume(memory <= 16384);
        kani::assume(cpus > 0 && cpus <= 128);

        let result = calculate_optimal_priority_verified(
            current_priority,
            target_priority,
            load,
            responsiveness,
            memory,
            cpus,
        );

        // Постусловия
        assert!(result >= MIN_PRIORITY);
        assert!(result <= MAX_PRIORITY);
    }

    /// Kani proof: монотонность снижения при высокой нагрузке
    #[kani::proof]
    fn verify_monotonic_decrease_under_load() {
        let current_priority: i32 = kani::any();
        let target_priority: i32 = kani::any();
        let load: f64 = kani::any();
        let cpus: usize = kani::any();

        kani::assume(MIN_PRIORITY <= current_priority && current_priority <= MAX_PRIORITY);
        kani::assume(MIN_PRIORITY <= target_priority && target_priority <= MAX_PRIORITY);
        kani::assume(cpus > 0 && cpus <= 128);
        kani::assume(load > (cpus as f64) * CRITICAL_LOAD_MULTIPLIER as f64);

        let result = calculate_optimal_priority_verified(
            current_priority,
            target_priority,
            load,
            0,
            8192,
            cpus,
        );

        assert!(result <= target_priority);
    }

    /// Kani proof: корректировка всегда уменьшает или сохраняет приоритет
    #[kani::proof]
    fn verify_adjustment_decreases() {
        let old_priority: i32 = kani::any();
        let step: i32 = kani::any();

        kani::assume(MIN_PRIORITY <= old_priority && old_priority <= MAX_PRIORITY);
        kani::assume(step > 0 && step <= 100);

        let result = apply_priority_adjustment(old_priority, step);

        assert!(result <= old_priority);
        assert!(result >= MIN_PRIORITY);
    }

    /// Kani proof: конечность корректировок
    #[kani::proof]
    #[kani::unwind(10)] // Ограничиваем развёртку цикла
    fn verify_finite_adjustments() {
        let mut priority: i32 = kani::any();
        kani::assume(MIN_PRIORITY <= priority && priority <= MAX_PRIORITY);

        let mut count = 0;
        while priority > MIN_PRIORITY && count < 10 {
            priority = apply_priority_adjustment(priority, 10);
            count += 1;
        }

        // После максимум 9 итераций должны достичь минимума
        // (95 - 10) / 10 = 8.5 => 9 итераций
        assert!(count <= 9 || priority == MIN_PRIORITY);
    }

    /// Kani proof: clamp всегда возвращает значение в границах
    #[kani::proof]
    fn verify_clamp_bounds() {
        let value: i32 = kani::any();
        let result = value.clamp(MIN_PRIORITY, MAX_PRIORITY);

        assert!(result >= MIN_PRIORITY);
        assert!(result <= MAX_PRIORITY);
    }

    /// Kani proof: композиция корректировок сохраняет инварианты
    #[kani::proof]
    fn verify_composition_preserves_invariants() {
        let priority: i32 = kani::any();
        let step1: i32 = kani::any();
        let step2: i32 = kani::any();

        kani::assume(MIN_PRIORITY <= priority && priority <= MAX_PRIORITY);
        kani::assume(step1 > 0 && step1 <= 20);
        kani::assume(step2 > 0 && step2 <= 20);

        // Применяем две корректировки подряд
        let after_first = apply_priority_adjustment(priority, step1);
        let after_second = apply_priority_adjustment(after_first, step2);

        // Инварианты должны сохраняться
        assert!(after_second >= MIN_PRIORITY);
        assert!(after_second <= MAX_PRIORITY);
        assert!(after_second <= priority);
    }

    /// Kani proof: независимость корректировок разных процессов
    #[kani::proof]
    fn verify_adjustment_independence() {
        let priority1: i32 = kani::any();
        let priority2: i32 = kani::any();
        let step: i32 = kani::any();

        kani::assume(MIN_PRIORITY <= priority1 && priority1 <= MAX_PRIORITY);
        kani::assume(MIN_PRIORITY <= priority2 && priority2 <= MAX_PRIORITY);
        kani::assume(step > 0 && step <= 20);

        // Корректировка процесса 1
        let result1 = apply_priority_adjustment(priority1, step);

        // Корректировка процесса 2 (независимо)
        let result2 = apply_priority_adjustment(priority2, step);

        // Результаты не должны влиять друг на друга
        assert!(result1 >= MIN_PRIORITY && result1 <= MAX_PRIORITY);
        assert!(result2 >= MIN_PRIORITY && result2 <= MAX_PRIORITY);

        // Если приоритеты были равны, результаты тоже равны
        if priority1 == priority2 {
            assert!(result1 == result2);
        }
    }

    /// Kani proof: балансировка нагрузки
    #[kani::proof]
    fn verify_load_balancing() {
        let priority1: i32 = kani::any();
        let priority2: i32 = kani::any();
        let load: f64 = kani::any();
        let cpus: usize = kani::any();

        kani::assume(MIN_PRIORITY <= priority1 && priority1 <= MAX_PRIORITY);
        kani::assume(MIN_PRIORITY <= priority2 && priority2 <= MAX_PRIORITY);
        kani::assume(cpus > 0 && cpus <= 128);
        kani::assume(load > (cpus as f64) * CRITICAL_LOAD_MULTIPLIER as f64);

        // При высокой нагрузке оба процесса должны снизить приоритет
        let result1 =
            calculate_optimal_priority_verified(priority1, priority1, load, 0, 8192, cpus);
        let result2 =
            calculate_optimal_priority_verified(priority2, priority2, load, 0, 8192, cpus);

        assert!(result1 <= priority1);
        assert!(result2 <= priority2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_bounds() {
        let result = calculate_optimal_priority_verified(50, 50, 0.0, 0, 8192, 4);
        assert!(result >= MIN_PRIORITY && result <= MAX_PRIORITY);
    }

    #[test]
    fn test_high_load_decreases_priority() {
        let result = calculate_optimal_priority_verified(80, 80, 90.0, 0, 8192, 4);
        assert!(result < 80);
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
}
