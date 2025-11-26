# Устранение проблем с TLA+ спецификацией

## Проблема: Нарушение temporal properties

### Симптомы
```
Temporal properties were violated.
The following behavior constitutes a counter-example:
...
16: Stuttering
```

### Причина

**Stuttering** - это когда система может бесконечно "ничего не делать" (оставаться в том же состоянии). В TLA+ это допустимое поведение по умолчанию.

Проблема возникла из-за:

1. **Отсутствие fairness constraint** - спецификация не гарантировала, что действие `AdjustPriority` будет выполнено, даже если оно возможно

2. **Слабое свойство живости** - свойство `PriorityDecreasesUnderLoad` требовало достижения конкретного значения, но система могла застрять раньше

### Контрпример

```
Шаг 1-7:  load растёт с 0 до 60 (priority = 95)
Шаг 8:    AdjustPriority: priority = 85
Шаг 9-10: load растёт до 80
Шаг 11-15: AdjustPriority несколько раз: priority = 35
Шаг 16:   STUTTERING - система застревает
```

Проблема: `load = 80 > 50` (критический порог), но `priority = 35 > 30` (MIN_PRIORITY + 20), и система больше ничего не делает.

## Решение

### 1. Добавление Weak Fairness

**Было:**
```tla
Spec == Init /\ [][Next]_vars
```

**Стало:**
```tla
Spec == Init /\ [][Next]_vars /\ WF_vars(AdjustPriority)
```

**Что это даёт:**
- `WF_vars(AdjustPriority)` означает "weak fairness для действия AdjustPriority"
- Гарантирует: если `AdjustPriority` **постоянно возможно**, оно **в конечном итоге выполнится**
- Предотвращает бесконечное игнорирование доступного действия

### 2. Улучшение свойства живости

**Было:**
```tla
PriorityDecreasesUnderLoad ==
    load > CRITICAL_LOAD ~> priority <= MIN_PRIORITY + 20
```

**Проблема:** Слишком конкретное требование - система может застрять на priority = 35

**Стало:**
```tla
PriorityDecreasesUnderLoad ==
    (load > CRITICAL_LOAD /\ priority > MIN_PRIORITY) ~> 
        (priority < MAX_PRIORITY \/ load <= CRITICAL_LOAD)
```

**Что это означает:**
- Если нагрузка высокая И приоритет не минимальный
- То в конечном итоге: приоритет снизится ИЛИ нагрузка упадёт

### 3. Добавление более сильного свойства

```tla
EventualMinPriority ==
    (load > CRITICAL_LOAD) ~> (priority = MIN_PRIORITY \/ load <= CRITICAL_LOAD)
```

**Что это означает:**
- Если нагрузка высокая, то в конечном итоге либо приоритет достигнет минимума, либо нагрузка снизится

## Результат

```
Model checking completed. No error has been found.
246 states generated, 110 distinct states found, 0 states left on queue.
Finished checking temporal properties in 00s
```

✅ Все инварианты выполнены  
✅ Все свойства живости выполнены  
✅ Нет дедлоков  
✅ Нет нарушений

## Типы Fairness в TLA+

### Weak Fairness (WF)
```tla
WF_vars(Action)
```
**Означает:** Если действие **постоянно возможно**, оно **в конечном итоге выполнится**

**Пример:** Если система постоянно перегружена, корректировка приоритета в конечном итоге произойдёт

### Strong Fairness (SF)
```tla
SF_vars(Action)
```
**Означает:** Если действие **бесконечно часто возможно**, оно **бесконечно часто выполнится**

**Пример:** Если система периодически перегружается, корректировка будет происходить каждый раз

### Когда использовать

- **WF** - для действий, которые должны выполниться, если условия стабильны
- **SF** - для действий, которые должны выполняться при периодических условиях
- **Без fairness** - для моделирования возможности бесконечного ожидания

## Общие ошибки и решения

### Ошибка 1: "Temporal properties were violated" + Stuttering

**Причина:** Отсутствие fairness constraint

**Решение:** Добавить `WF_vars(Action)` или `SF_vars(Action)` в Spec

### Ошибка 2: "Deadlock reached"

**Причина:** Нет доступных действий в некотором состоянии

**Решение:** 
- Добавить действие, которое всегда возможно (например, UpdateSystemState)
- Или это реальный дедлок в логике

### Ошибка 3: Свойство живости не выполняется даже с fairness

**Причина:** Свойство слишком сильное или неправильно сформулировано

**Решение:**
- Ослабить свойство (добавить альтернативы через `\/`)
- Проверить, что свойство действительно должно выполняться

### Ошибка 4: "State space too large"

**Причина:** Слишком много возможных состояний

**Решение:**
- Добавить CONSTRAINT в .cfg файл
- Уменьшить диапазоны констант
- Использовать симметрию (SYMMETRY)

## Проверка спецификации

### Базовая проверка
```bash
java -cp tla2tools.jar tlc2.TLC PriorityManagerSimple
```

### С покрытием
```bash
java -cp tla2tools.jar tlc2.TLC -coverage 1 PriorityManagerSimple
```

### Симуляция (случайные трассы)
```bash
java -cp tla2tools.jar tlc2.TLC -simulate PriorityManagerSimple
```

### С детальным выводом
```bash
java -cp tla2tools.jar tlc2.TLC -verbose PriorityManagerSimple
```

## Интерпретация результатов

### ✅ Успех
```
Model checking completed. No error has been found.
```
Все свойства выполнены для всех достижимых состояний.

### ❌ Нарушение инварианта
```
Error: Invariant PriorityInBounds is violated.
```
Найдено состояние, где инвариант не выполняется. TLC покажет трассу.

### ❌ Нарушение свойства живости
```
Temporal properties were violated.
```
Найдена трасса, где свойство живости не выполняется (часто с stuttering).

### ⚠️ Предупреждение о fairness
```
Temporal properties are being verified without a fairness constraint...
```
Рекомендуется добавить fairness, иначе могут быть тривиальные контрпримеры.

## Рекомендации

1. **Всегда добавляйте fairness** для свойств живости
2. **Начинайте с простых моделей** и постепенно усложняйте
3. **Проверяйте инварианты отдельно** от свойств живости
4. **Используйте CONSTRAINT** для ограничения пространства состояний
5. **Читайте контрпримеры внимательно** - они показывают реальные проблемы

## Дополнительные ресурсы

- [TLA+ Hyperbook - Fairness](https://learntla.com/temporal-logic/fairness/)
- [Specifying Systems - Chapter 8](https://lamport.azurewebsites.net/tla/book.html)
- [TLA+ Examples](https://github.com/tlaplus/Examples)
