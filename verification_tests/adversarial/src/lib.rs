// Adversarial тесты - попытка сломать систему!

pub mod broken;

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
mod adversarial_tests {
    use super::*;
    use proptest::prelude::*;

    // 🔨 ТЕСТ 1: Экстремальные значения
    #[test]
    fn test_extreme_values() {
        // Максимальные значения
        let r1 = calculate_optimal_priority(i32::MAX, f64::MAX, u64::MAX, u64::MAX, usize::MAX);
        assert!(r1 >= MIN_PRIORITY && r1 <= MAX_PRIORITY, "Failed with MAX values");

        // Минимальные значения
        let r2 = calculate_optimal_priority(i32::MIN, f64::MIN, 0, 0, 0);
        assert!(r2 >= MIN_PRIORITY && r2 <= MAX_PRIORITY, "Failed with MIN values");

        // Нулевые значения
        let r3 = calculate_optimal_priority(0, 0.0, 0, 0, 0);
        assert!(r3 >= MIN_PRIORITY && r3 <= MAX_PRIORITY, "Failed with zeros");
    }

    // 🔨 ТЕСТ 2: Отрицательные значения
    #[test]
    fn test_negative_values() {
        let r1 = calculate_optimal_priority(-100, -50.0, 0, 0, 0);
        assert!(r1 >= MIN_PRIORITY && r1 <= MAX_PRIORITY, "Failed with negative priority");

        let r2 = apply_priority_adjustment(-50, -100);
        assert!(r2 >= MIN_PRIORITY, "Failed with negative adjustment");
    }

    // 🔨 ТЕСТ 3: Переполнение
    #[test]
    fn test_overflow() {
        // Попытка переполнения при вычитании
        let r1 = apply_priority_adjustment(MIN_PRIORITY, i32::MAX);
        assert!(r1 >= MIN_PRIORITY, "Overflow in subtraction");

        // Попытка переполнения при сложении
        let r2 = calculate_optimal_priority(i32::MAX - 1, 0.0, 0, u64::MAX, 1);
        assert!(r2 <= MAX_PRIORITY, "Overflow in addition");
    }

    // 🔨 ТЕСТ 4: NaN и Infinity
    #[test]
    fn test_nan_infinity() {
        let r1 = calculate_optimal_priority(50, f64::NAN, 0, 1000, 4);
        assert!(r1 >= MIN_PRIORITY && r1 <= MAX_PRIORITY, "Failed with NaN");

        let r2 = calculate_optimal_priority(50, f64::INFINITY, 0, 1000, 4);
        assert!(r2 >= MIN_PRIORITY && r2 <= MAX_PRIORITY, "Failed with INFINITY");

        let r3 = calculate_optimal_priority(50, f64::NEG_INFINITY, 0, 1000, 4);
        assert!(r3 >= MIN_PRIORITY && r3 <= MAX_PRIORITY, "Failed with NEG_INFINITY");
    }

    // 🔨 ТЕСТ 5: Деление на ноль
    #[test]
    fn test_division_by_zero() {
        // num_cpus = 0 может вызвать деление на ноль
        let r = calculate_optimal_priority(50, 100.0, 0, 1000, 0);
        assert!(r >= MIN_PRIORITY && r <= MAX_PRIORITY, "Failed with zero CPUs");
    }

    // 🔨 ТЕСТ 6: Очень большие шаги
    #[test]
    fn test_huge_steps() {
        let r1 = apply_priority_adjustment(95, 1000000);
        assert_eq!(r1, MIN_PRIORITY, "Should reach minimum with huge step");

        let r2 = apply_priority_adjustment(95, i32::MAX);
        assert_eq!(r2, MIN_PRIORITY, "Should reach minimum with MAX step");
    }

    // 🔨 ТЕСТ 7: Граничные значения
    #[test]
    fn test_boundary_values() {
        // Ровно на границе
        let r1 = calculate_optimal_priority(MIN_PRIORITY, 0.0, 0, 1000, 4);
        assert_eq!(r1, MIN_PRIORITY);

        let r2 = calculate_optimal_priority(MAX_PRIORITY, 0.0, 0, 1000, 4);
        assert_eq!(r2, MAX_PRIORITY);

        // Чуть за границей
        let r3 = calculate_optimal_priority(MIN_PRIORITY - 1, 0.0, 0, 1000, 4);
        assert!(r3 >= MIN_PRIORITY);

        let r4 = calculate_optimal_priority(MAX_PRIORITY + 1, 0.0, 0, 1000, 4);
        assert!(r4 <= MAX_PRIORITY);
    }

    // 🔨 ТЕСТ 8: Противоречивые условия
    #[test]
    fn test_contradictory_conditions() {
        // Все условия для снижения приоритета одновременно
        let r = calculate_optimal_priority(
            95,
            1000.0,  // Очень высокая нагрузка
            10000,   // Очень плохая реактивность
            0,       // Нет памяти
            1        // Один CPU
        );
        assert!(r >= MIN_PRIORITY && r <= MAX_PRIORITY);
        assert!(r < 95, "Should decrease priority");
    }

    // 🔨 ТЕСТ 9: Быстрая последовательность корректировок
    #[test]
    fn test_rapid_adjustments() {
        let mut priority = MAX_PRIORITY;
        
        // 1000 корректировок подряд
        for _ in 0..1000 {
            priority = apply_priority_adjustment(priority, 1);
            assert!(priority >= MIN_PRIORITY && priority <= MAX_PRIORITY);
        }
        
        assert_eq!(priority, MIN_PRIORITY, "Should reach minimum after many adjustments");
    }

    // 🔨 ТЕСТ 10: Случайные невалидные данные (fuzzing)
    proptest! {
        #[test]
        fn fuzz_calculate_priority(
            priority in i32::MIN..i32::MAX,
            load in -1000.0..10000.0,
            responsiveness in 0u64..u64::MAX,
            memory in 0u64..u64::MAX,
            cpus in 0usize..1000
        ) {
            let result = calculate_optimal_priority(priority, load, responsiveness, memory, cpus);
            
            // Инвариант должен ВСЕГДА выполняться
            prop_assert!(result >= MIN_PRIORITY, "Result {} < MIN_PRIORITY", result);
            prop_assert!(result <= MAX_PRIORITY, "Result {} > MAX_PRIORITY", result);
        }
    }

    // 🔨 ТЕСТ 11: Fuzzing корректировок
    proptest! {
        #[test]
        fn fuzz_adjustments(
            priority in i32::MIN..i32::MAX,
            step in i32::MIN..i32::MAX
        ) {
            let result = apply_priority_adjustment(priority, step);
            
            // Инвариант должен ВСЕГДА выполняться
            prop_assert!(result >= MIN_PRIORITY, "Result {} < MIN_PRIORITY", result);
        }
    }

    // 🔨 ТЕСТ 12: Стресс-тест с экстремальными комбинациями
    #[test]
    fn stress_test_extreme_combinations() {
        let test_cases = vec![
            // (priority, load, responsiveness, memory, cpus)
            (i32::MAX, f64::MAX, u64::MAX, u64::MAX, usize::MAX),
            (i32::MIN, f64::MIN, 0, 0, 0),
            (0, f64::NAN, 0, 0, 0),
            (0, f64::INFINITY, 0, 0, 0),
            (-1000, -1000.0, 0, 0, 0),
            (1000000, 1000000.0, u64::MAX, 0, 0),
        ];

        for (i, (p, l, r, m, c)) in test_cases.iter().enumerate() {
            let result = calculate_optimal_priority(*p, *l, *r, *m, *c);
            assert!(
                result >= MIN_PRIORITY && result <= MAX_PRIORITY,
                "Test case {} failed: priority={}, load={}, result={}",
                i, p, l, result
            );
        }
    }

    // 🔨 ТЕСТ 13: Проверка на панику
    #[test]
    fn test_no_panics() {
        // Эти вызовы НЕ должны вызывать панику
        let _ = std::panic::catch_unwind(|| {
            calculate_optimal_priority(i32::MAX, f64::NAN, u64::MAX, 0, 0)
        });

        let _ = std::panic::catch_unwind(|| {
            apply_priority_adjustment(i32::MIN, i32::MAX)
        });
    }
}
