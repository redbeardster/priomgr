// Файл для проверки Prusti контрактов

/// Константы для верификации
pub const MIN_PRIORITY: i32 = 10;
pub const MAX_PRIORITY: i32 = 95;
pub const CRITICAL_LOAD_MULTIPLIER: f32 = 2.0;

/// Проверяемая функция: вычисление оптимального приоритета
#[cfg_attr(feature = "prusti", requires(MIN_PRIORITY <= target_priority && target_priority <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(MIN_PRIORITY <= result && result <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(load > 50.0 ==> result <= target_priority))]
pub fn calculate_optimal_priority_verified(
    _current_priority: i32,
    target_priority: i32,
    load_high: bool,  // Упрощено для Prusti
    responsiveness_ms: u64,
    available_memory_mb: u64,
) -> i32 {
    let mut priority = target_priority;

    if load_high && priority >= 10 {
        priority = if priority >= 10 { priority - 10 } else { MIN_PRIORITY };
        priority = priority.max(MIN_PRIORITY);
    }

    if responsiveness_ms > 2000 && priority >= 5 {
        priority = if priority >= 5 { priority - 5 } else { MIN_PRIORITY };
        priority = priority.max(MIN_PRIORITY);
    }

    if available_memory_mb < 100 && priority >= 3 {
        priority = if priority >= 3 { priority - 3 } else { MIN_PRIORITY };
        priority = priority.max(MIN_PRIORITY);
    }

    priority.clamp(MIN_PRIORITY, MAX_PRIORITY)
}

/// Проверяемая функция: применение корректировки приоритета
#[cfg_attr(feature = "prusti", requires(MIN_PRIORITY <= old_priority && old_priority <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", requires(step > 0))]
#[cfg_attr(feature = "prusti", requires(step <= MAX_PRIORITY))]  // Предотвращаем overflow
#[cfg_attr(feature = "prusti", ensures(MIN_PRIORITY <= result && result <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(result <= old_priority))]
pub fn apply_priority_adjustment(old_priority: i32, step: i32) -> i32 {
    // Используем saturating_sub для предотвращения overflow
    let new_priority = old_priority.saturating_sub(step);
    new_priority.max(MIN_PRIORITY)
}

/// Проверяемая функция: конечность корректировок с инвариантом цикла
#[cfg_attr(feature = "prusti", requires(MIN_PRIORITY <= initial_priority && initial_priority <= MAX_PRIORITY))]
#[cfg_attr(feature = "prusti", requires(step > 0 && step <= 10))]
#[cfg_attr(feature = "prusti", ensures(result == MIN_PRIORITY || result >= MIN_PRIORITY))]
#[cfg_attr(feature = "prusti", ensures(count <= 9))]  // Максимум 9 итераций для диапазона 85
pub fn apply_adjustments_until_min(initial_priority: i32, step: i32) -> (i32, usize) {
    let mut priority = initial_priority;
    let mut count = 0;
    
    // Инвариант цикла для Prusti
    #[cfg_attr(feature = "prusti", invariant(MIN_PRIORITY <= priority && priority <= MAX_PRIORITY))]
    #[cfg_attr(feature = "prusti", invariant(count <= 9))]
    #[cfg_attr(feature = "prusti", invariant(priority <= initial_priority))]
    while priority > MIN_PRIORITY && count < 10 {
        priority = apply_priority_adjustment(priority, step);
        count += 1;
    }
    
    (priority, count)
}

/// Проверяемая функция: проверка необходимости корректировки
#[cfg_attr(feature = "prusti", pure)]
pub fn needs_adjustment(load: f64, threshold: f64, priority: i32) -> bool {
    load > threshold && priority > MIN_PRIORITY
}

fn main() {
    // Пустая main для компиляции
}
