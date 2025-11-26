// Property-based тесты для Priority Manager

pub const MIN_PRIORITY: i32 = 10;
pub const MAX_PRIORITY: i32 = 95;

pub fn calculate_optimal_priority(
    target_priority: i32,
    load: f64,
    responsiveness_ms: u64,
    available_memory_mb: u64,
    num_cpus: usize,
) -> i32 {
    let mut priority = target_priority;

    if load > (num_cpus as f64) * 2.0 {
        priority = (priority - 10).max(MIN_PRIORITY);
    }

    if responsiveness_ms > 2000 {
        priority = (priority - 5).max(MIN_PRIORITY);
    }

    if available_memory_mb < 100 {
        priority = (priority - 3).max(MIN_PRIORITY);
    }

    priority.clamp(MIN_PRIORITY, MAX_PRIORITY)
}

pub fn apply_priority_adjustment(old_priority: i32, step: i32) -> i32 {
    (old_priority - step).max(MIN_PRIORITY)
}

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;

    // S1: Ограниченность приоритетов
    proptest! {
        #[test]
        fn priority_always_in_bounds(
            initial_priority in MIN_PRIORITY..=MAX_PRIORITY,
            load in 0.0..100.0,
            responsiveness in 0u64..10000,
            memory in 0u64..16384,
            cpus in 1usize..128
        ) {
            let adjusted = calculate_optimal_priority(
                initial_priority,
                load,
                responsiveness,
                memory,
                cpus
            );
            prop_assert!(adjusted >= MIN_PRIORITY);
            prop_assert!(adjusted <= MAX_PRIORITY);
        }
    }

    // S2: Монотонность при высокой нагрузке
    proptest! {
        #[test]
        fn priority_decreases_under_high_load(
            initial_priority in MIN_PRIORITY..=MAX_PRIORITY,
            cpus in 1usize..128
        ) {
            let high_load = (cpus as f64) * 2.5; // Выше порога
            let adjusted = calculate_optimal_priority(
                initial_priority,
                high_load,
                0,
                8192,
                cpus
            );
            prop_assert!(adjusted <= initial_priority);
        }
    }

    // S2: Корректировка всегда уменьшает приоритет
    proptest! {
        #[test]
        fn adjustment_decreases_priority(
            priority in MIN_PRIORITY..=MAX_PRIORITY,
            step in 1i32..=50
        ) {
            let result = apply_priority_adjustment(priority, step);
            prop_assert!(result <= priority);
            prop_assert!(result >= MIN_PRIORITY);
        }
    }

    // P1: Конечность корректировок
    proptest! {
        #[test]
        fn adjustments_are_finite(
            mut priority in MIN_PRIORITY..=MAX_PRIORITY,
            step in 1i32..=20
        ) {
            let mut count = 0;
            while priority > MIN_PRIORITY && count < 100 {
                priority = apply_priority_adjustment(priority, step);
                count += 1;
            }
            // Должны достичь минимума за разумное количество шагов
            prop_assert!(count <= (MAX_PRIORITY - MIN_PRIORITY) / step + 1);
        }
    }

    // C2: Композиция сохраняет инварианты
    proptest! {
        #[test]
        fn composition_preserves_invariants(
            priority in MIN_PRIORITY..=MAX_PRIORITY,
            step1 in 1i32..=20,
            step2 in 1i32..=20
        ) {
            let after_first = apply_priority_adjustment(priority, step1);
            let after_second = apply_priority_adjustment(after_first, step2);
            
            prop_assert!(after_second >= MIN_PRIORITY);
            prop_assert!(after_second <= MAX_PRIORITY);
            prop_assert!(after_second <= priority);
        }
    }

    // C1: Независимость корректировок
    proptest! {
        #[test]
        fn adjustments_are_independent(
            priority1 in MIN_PRIORITY..=MAX_PRIORITY,
            priority2 in MIN_PRIORITY..=MAX_PRIORITY,
            step in 1i32..=20
        ) {
            let result1 = apply_priority_adjustment(priority1, step);
            let result2 = apply_priority_adjustment(priority2, step);
            
            prop_assert!(result1 >= MIN_PRIORITY && result1 <= MAX_PRIORITY);
            prop_assert!(result2 >= MIN_PRIORITY && result2 <= MAX_PRIORITY);
            
            // Если входы равны, выходы тоже равны
            if priority1 == priority2 {
                prop_assert_eq!(result1, result2);
            }
        }
    }

    // S4: Балансировка нагрузки
    proptest! {
        #[test]
        fn load_balancing_works(
            priority1 in MIN_PRIORITY..=MAX_PRIORITY,
            priority2 in MIN_PRIORITY..=MAX_PRIORITY,
            cpus in 1usize..128
        ) {
            let high_load = (cpus as f64) * 2.5;
            
            let result1 = calculate_optimal_priority(priority1, high_load, 0, 8192, cpus);
            let result2 = calculate_optimal_priority(priority2, high_load, 0, 8192, cpus);
            
            // Оба процесса должны снизить приоритет
            prop_assert!(result1 <= priority1);
            prop_assert!(result2 <= priority2);
        }
    }

    // S1: Clamp всегда работает корректно
    proptest! {
        #[test]
        fn clamp_always_bounds(value in -1000i32..1000) {
            let result = value.clamp(MIN_PRIORITY, MAX_PRIORITY);
            prop_assert!(result >= MIN_PRIORITY);
            prop_assert!(result <= MAX_PRIORITY);
        }
    }

    // Комбинированный тест: множественные корректировки
    proptest! {
        #[test]
        fn multiple_adjustments_preserve_invariants(
            mut priority in MIN_PRIORITY..=MAX_PRIORITY,
            steps in prop::collection::vec(1i32..=10, 1..20)
        ) {
            for step in steps {
                priority = apply_priority_adjustment(priority, step);
                prop_assert!(priority >= MIN_PRIORITY);
                prop_assert!(priority <= MAX_PRIORITY);
            }
        }
    }
}
