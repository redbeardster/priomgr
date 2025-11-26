# Шпаргалка по контрактам Kani и Prusti

## 🟣 Prusti - Быстрая справка

### Основные аннотации

```rust
#[requires(условие)]     // Предусловие - что должно быть истинно ДО вызова
#[ensures(условие)]      // Постусловие - что гарантируется ПОСЛЕ вызова
#[pure]                  // Функция без побочных эффектов
```

### Специальные переменные

```rust
result                   // Возвращаемое значение в ensures
old(expr)               // Значение выражения ДО выполнения функции
```

### Логические операторы

```rust
&&                      // И (AND)
||                      // ИЛИ (OR)
!                       // НЕ (NOT)
==>                     // Импликация (если... то...)
<==                     // Обратная импликация
<==>                    // Эквивалентность (тогда и только тогда)
```

### Квантификаторы

```rust
forall(|x: T| условие)  // Для всех x типа T
exists(|x: T| условие)  // Существует x типа T
```

### Примеры

```rust
// Простой контракт
#[requires(x > 0)]
#[ensures(result > 0)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

// С импликацией
#[requires(x >= 0)]
#[ensures(x > 10 ==> result == x - 10)]
#[ensures(x <= 10 ==> result == 0)]
pub fn saturating_sub(x: i32) -> i32 {
    if x > 10 { x - 10 } else { 0 }
}

// С old()
#[requires(balance >= amount)]
#[ensures(result == old(balance) - amount)]
pub fn withdraw(balance: u64, amount: u64) -> u64 {
    balance - amount
}

// Pure функция
#[pure]
pub fn is_valid(x: i32) -> bool {
    x >= 0 && x <= 100
}

// Использование pure в контракте
#[requires(is_valid(x))]
#[ensures(is_valid(result))]
pub fn process(x: i32) -> i32 {
    x.clamp(0, 100)
}
```

---

## 🟢 Kani - Быстрая справка

### Основные функции

```rust
kani::any::<T>()        // Создать символьное значение типа T
kani::assume(условие)   // Ограничить пространство проверки
assert!(условие)        // Проверить постусловие
```

### Аннотации

```rust
#[kani::proof]          // Отметить функцию как proof
#[kani::unwind(N)]      // Развернуть циклы максимум N раз
```

### Примеры

```rust
// Простой proof
#[kani::proof]
fn verify_increment() {
    let x: i32 = kani::any();
    kani::assume(x > 0 && x < i32::MAX);
    
    let result = increment(x);
    
    assert!(result > 0);
}

// С циклом
#[kani::proof]
#[kani::unwind(10)]
fn verify_loop() {
    let mut x: i32 = kani::any();
    kani::assume(x >= 0 && x <= 100);
    
    let mut count = 0;
    while x > 0 && count < 10 {
        x = x / 2;
        count += 1;
    }
    
    assert!(x == 0 || count == 10);
}

// Проверка граничных случаев
#[kani::proof]
fn verify_edge_cases() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    
    kani::assume(x <= 200);
    kani::assume(y <= 200);
    
    let result = x.saturating_add(y);
    
    assert!(result >= x);
    assert!(result >= y);
}
```

---

## 🔄 Перевод между Prusti и Kani

### Prusti → Kani

```rust
// Prusti
#[requires(x > 0)]
#[ensures(result > 0)]
pub fn f(x: i32) -> i32 { x + 1 }

// ↓ ↓ ↓

// Kani
#[kani::proof]
fn verify_f() {
    let x: i32 = kani::any();
    kani::assume(x > 0);  // requires
    
    let result = f(x);
    
    assert!(result > 0);  // ensures
}
```

### Импликация

```rust
// Prusti
#[ensures(x > 10 ==> result > 0)]

// ↓ ↓ ↓

// Kani
if x > 10 {
    assert!(result > 0);
}
```

---

## 📊 Сравнение синтаксиса

| Концепция | Prusti | Kani |
|-----------|--------|------|
| Предусловие | `#[requires(x > 0)]` | `kani::assume(x > 0)` |
| Постусловие | `#[ensures(result > 0)]` | `assert!(result > 0)` |
| Символьное значение | - | `kani::any::<i32>()` |
| Импликация | `x > 0 ==> y > 0` | `if x > 0 { assert!(y > 0) }` |
| Для всех | `forall(\|i\| ...)` | Цикл + assert |
| Старое значение | `old(x)` | Сохранить в переменную |
| Pure функция | `#[pure]` | Обычная функция |

---

## 💡 Типичные паттерны

### Проверка границ

```rust
// Prusti
#[requires(MIN <= x && x <= MAX)]
#[ensures(MIN <= result && result <= MAX)]

// Kani
kani::assume(MIN <= x && x <= MAX);
assert!(MIN <= result && result <= MAX);
```

### Монотонность

```rust
// Prusti
#[ensures(result <= x)]

// Kani
assert!(result <= x);
```

### Условная корректность

```rust
// Prusti
#[ensures(condition ==> result == expected)]

// Kani
if condition {
    assert!(result == expected);
}
```

### Инвариант цикла

```rust
// Prusti
#[invariant(sum == i * (i + 1) / 2)]
while i < n {
    i += 1;
    sum += i;
}

// Kani
#[kani::unwind(N)]
while i < n {
    // Проверить инвариант вручную
    assert!(sum == i * (i + 1) / 2);
    i += 1;
    sum += i;
}
```

---

## 🎯 Когда использовать что

### Используйте Prusti для:

```rust
// ✅ Документирования контрактов
#[requires(balance >= amount)]
#[ensures(result.balance == old(balance) - amount)]
pub fn withdraw(balance: u64, amount: u64) -> Account

// ✅ Композиции функций
#[pure]
fn is_sorted(v: &[i32]) -> bool { ... }

#[requires(is_sorted(input))]
#[ensures(is_sorted(result))]
pub fn merge(input: &[i32]) -> Vec<i32>

// ✅ Сложных спецификаций
#[ensures(forall(|i: usize| i < result.len() ==> result[i] >= 0))]
pub fn all_positive(v: Vec<i32>) -> Vec<i32>
```

### Используйте Kani для:

```rust
// ✅ Быстрой проверки без аннотаций
#[kani::proof]
fn verify_quick() {
    let x: i32 = kani::any();
    let r = my_function(x);
    assert!(r >= 0);
}

// ✅ Поиска граничных случаев
#[kani::proof]
fn find_overflow() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let r = x + y;  // Найдёт переполнение
    assert!(r >= x);
}

// ✅ Проверки алгоритмов
#[kani::proof]
#[kani::unwind(10)]
fn verify_algorithm() {
    let mut x: i32 = kani::any();
    while x > 0 { x = x / 2; }
    assert!(x == 0);
}
```

---

## 🚀 Быстрый старт

### Prusti

```bash
# Установка
cargo install prusti-cli

# Проверка
cargo prusti

# Или напрямую
prusti-rustc src/lib.rs
```

### Kani

```bash
# Установка
cargo install --locked kani-verifier
cargo kani setup

# Проверка
cargo kani

# Конкретный proof
cargo kani --harness verify_my_function
```

---

## 📚 Полезные ссылки

- [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/)
- [Kani Book](https://model-checking.github.io/kani/)
- [CONTRACTS_EXPLAINED.md](CONTRACTS_EXPLAINED.md) - детальные объяснения
- [KANI_VS_PRUSTI.md](KANI_VS_PRUSTI.md) - сравнение подходов

---

## 🎓 Примеры из Priority Manager

### Prusti контракт

```rust
#[requires(MIN_PRIORITY <= old_priority && old_priority <= MAX_PRIORITY)]
#[requires(step > 0)]
#[ensures(MIN_PRIORITY <= result && result <= MAX_PRIORITY)]
#[ensures(result <= old_priority)]
pub fn apply_priority_adjustment(old_priority: i32, step: i32) -> i32 {
    (old_priority - step).max(MIN_PRIORITY)
}
```

### Kani proof

```rust
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
```

---

**Совет:** Начните с Kani для быстрой проверки, затем добавьте Prusti контракты для документации! 🎯
