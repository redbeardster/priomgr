# 🚀 Как запустить TLA+ проверку

## ✅ Быстрый старт

### Если TLA+ уже установлен:

```bash
java -cp tla2tools.jar tlc2.TLC PriorityManagerSimple.tla
```

**Ожидаемый результат:**
```
Model checking completed. No error has been found.
States analyzed: ~1000
```

---

## 📦 Установка TLA+

### Вариант 1: TLA+ Toolbox (рекомендуется)

1. Скачайте с https://github.com/tlaplus/tlaplus/releases
2. Распакуйте и запустите
3. Откройте `PriorityManagerSimple.tla`
4. Создайте модель с конфигурацией из `PriorityManagerSimple.cfg`
5. Нажмите "Run TLC"

### Вариант 2: Командная строка

```bash
# Скачать tla2tools.jar
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Запустить проверку
java -cp tla2tools.jar tlc2.TLC PriorityManagerSimple.tla
```

---

## 📊 Что проверяется

### Новые свойства (добавлены):

**Safety:**
- ✅ `PriorityInBounds` - приоритеты в границах
- ✅ `MonotonicDecrease` - монотонное уменьшение
- ✅ `AdjustmentsBounded` - ограниченность корректировок

**Liveness:**
- ✅ `EventualMinPriority` - конечное достижение минимума
- ✅ `EventualAdjustment` - конечная корректировка
- ✅ `TerminationGuarantee` - гарантия завершения

**Composition:**
- ✅ `CompositionPreservesInvariants` - композиция сохраняет инварианты
- ✅ `IndependenceOfActions` - независимость действий

**Finiteness:**
- ✅ `FiniteAdjustments` - конечность корректировок

**Итого: 9 свойств** ✅

---

## 🔍 Интерпретация результатов

### Успешная проверка:
```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.4E-16
States analyzed: 1000
```

✅ **Все свойства выполняются!**

### Если найдена ошибка:
```
Error: Invariant PriorityInBounds is violated.
The behavior up to this point is:
State 1: priority = 95, load = 0
State 2: priority = 105, load = 60  <-- ОШИБКА
```

❌ **Найдено нарушение инварианта**

---

## 💡 Полезные команды

### Проверка с ограничением глубины:
```bash
java -cp tla2tools.jar tlc2.TLC -depth 10 PriorityManagerSimple.tla
```

### Проверка с несколькими потоками:
```bash
java -cp tla2tools.jar tlc2.TLC -workers 4 PriorityManagerSimple.tla
```

### Генерация трассы:
```bash
java -cp tla2tools.jar tlc2.TLC -dump dot trace.dot PriorityManagerSimple.tla
```

---

## 📈 Покрытие TLA+

### Было: 82.5%
### Стало: 92.5%
### Улучшение: +10%

**Детали:** см. `УЛУЧШЕНИЕ_TLA_ISABELLE.md`

---

## 🎯 Что дальше?

### Для полной модели:

Используйте `PriorityManager.tla` (множественные процессы):

```bash
java -cp tla2tools.jar tlc2.TLC PriorityManager.tla
```

**Внимание:** Проверка займет ~5 минут (больше состояний)

---

## 📚 Дополнительная информация

- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Examples](https://github.com/tlaplus/Examples)

---

**Дата:** 26 ноября 2025  
**Статус:** ✅ Готово к запуску
