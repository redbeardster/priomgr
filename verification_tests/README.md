# 🔬 Тесты верификации Priority Manager

Этот каталог содержит изолированные тесты для проверки покрытия формальной верификацией.

## 📁 Структура

```
verification_tests/
├── prusti/              # Prusti deductive verification
│   ├── Cargo.toml
│   └── src/lib.rs
├── kani/                # Kani bounded model checking
│   ├── Cargo.toml
│   └── src/lib.rs
├── property_tests/      # Property-based тесты (PropTest)
│   ├── Cargo.toml
│   └── src/lib.rs
├── spin/                # SPIN model checker (liveness)
│   └── priority_manager.pml
├── uppaal/              # UPPAAL timed automata
│   └── priority_manager.xml
├── run_all_tests.sh     # Скрипт для запуска всех тестов
├── SPIN_UPPAAL_GUIDE.md # Руководство по SPIN и UPPAAL
└── README.md            # Этот файл
```

## 🚀 Быстрый старт

### Запуск всех тестов

```bash
cd verification_tests
./run_all_tests.sh
```

### Запуск отдельных тестов

#### Property-based тесты (всегда работают)
```bash
cd property_tests
cargo test --release
```

#### Prusti (требует установки)
```bash
cd prusti
cargo prusti --features prusti
```

#### Kani (требует установки)
```bash
cd kani
cargo kani
```

## 📦 Установка инструментов

### Prusti
```bash
cargo install prusti-cli
```

### Kani
```bash
cargo install --locked kani-verifier
cargo kani setup
```

### PropTest
Уже включен в зависимости, установка не требуется.

## 📊 Проверяемые свойства

### Safety Properties (Безопасность)

- **S1**: Приоритеты в границах [10, 95]
  - ✅ Prusti: контракты `requires`/`ensures`
  - ✅ Kani: `verify_priority_bounds`
  - ✅ PropTest: `priority_always_in_bounds`

- **S2**: Монотонность при стрессе
  - ✅ Prusti: контракт `ensures(result <= old_priority)`
  - ✅ Kani: `verify_monotonic_decrease_under_load`
  - ✅ PropTest: `priority_decreases_under_high_load`

- **S4**: Балансировка нагрузки
  - ✅ Kani: `verify_load_balancing`
  - ✅ PropTest: `load_balancing_works`

- **S5**: Отсутствие overflow
  - ✅ Prusti: использование `saturating_sub`
  - ✅ Kani: `verify_no_overflow`

### Finiteness (Конечность)

- **P1**: Конечность корректировок
  - ✅ Prusti: `apply_adjustments_until_min` с инвариантами цикла
  - ✅ Kani: `verify_finite_adjustments` с `#[kani::unwind(10)]`
  - ✅ PropTest: `adjustments_are_finite`

### Composition (Композиция)

- **C1**: Независимость корректировок
  - ✅ Kani: `verify_adjustment_independence`
  - ✅ PropTest: `adjustments_are_independent`

- **C2**: Композиция сохраняет инварианты
  - ✅ Prusti: `compose_adjustments`
  - ✅ Kani: `verify_composition_preserves_invariants`
  - ✅ PropTest: `composition_preserves_invariants`

## 📈 Покрытие по методам

| Свойство | Prusti | Kani | PropTest | Покрытие |
|----------|--------|------|----------|----------|
| S1: Границы приоритетов | ✅ | ✅ | ✅ | 100% |
| S2: Монотонность | ✅ | ✅ | ✅ | 100% |
| S4: Балансировка | ⚠️ | ✅ | ✅ | 67% |
| S5: Overflow | ✅ | ✅ | ⚠️ | 67% |
| P1: Конечность | ✅ | ✅ | ✅ | 100% |
| C1: Независимость | ⚠️ | ✅ | ✅ | 67% |
| C2: Композиция | ✅ | ✅ | ✅ | 100% |

**Общее покрытие: ~86%** (без учета Liveness)

## 🎯 Ожидаемые результаты

### Property-based тесты
```
running 9 tests
test property_tests::adjustments_are_finite ... ok
test property_tests::adjustments_are_independent ... ok
test property_tests::clamp_always_bounds ... ok
test property_tests::composition_preserves_invariants ... ok
test property_tests::load_balancing_works ... ok
test property_tests::multiple_adjustments_preserve_invariants ... ok
test property_tests::priority_always_in_bounds ... ok
test property_tests::priority_decreases_under_high_load ... ok
test property_tests::adjustment_decreases_priority ... ok

test result: ok. 9 passed; 0 failed
```

### Prusti
```
Verification successful
```

### Kani
```
VERIFICATION:- SUCCESSFUL
```

## 🔍 Отладка

### Prusti не работает?
```bash
# Проверьте установку
cargo prusti --version

# Попробуйте с verbose
cargo prusti --features prusti -v
```

### Kani не работает?
```bash
# Проверьте установку
cargo kani --version

# Попробуйте с одним proof
cargo kani --harness verify_priority_bounds
```

### PropTest падает?
```bash
# Запустите с verbose
cargo test -- --nocapture

# Запустите конкретный тест
cargo test priority_always_in_bounds
```

## 📚 Дополнительная информация

- [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/)
- [Kani Tutorial](https://model-checking.github.io/kani/tutorial.html)
- [PropTest Book](https://altsysrq.github.io/proptest-book/)

## 🎓 Интерпретация результатов

### Все тесты прошли ✅
Покрытие верификацией: **~86%** (отлично!)

### Prusti не установлен ⚠️
Покрытие: **~70%** (хорошо, но можно лучше)

### Только PropTest ⚠️
Покрытие: **~40%** (базовый уровень)

## 💡 Советы

1. **Начните с PropTest** - они всегда работают и не требуют установки
2. **Установите Kani** - дает сильные гарантии для bounded проверок
3. **Попробуйте Prusti** - для математических доказательств

## 🏆 Цель

**Достичь 90%+ покрытия** комбинацией всех трех методов!

---

**Дата создания:** 26 ноября 2025  
**Версия:** 1.0  
**Статус:** Готово к использованию ✓
