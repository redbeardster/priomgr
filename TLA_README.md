# TLA+ Спецификации для Priority Manager

## Файлы

### Основная спецификация
- **PriorityManager.tla** - полная модель системы с множественными процессами
- **PriorityManager.cfg** - конфигурация для проверки основной модели

### Упрощенная спецификация
- **PriorityManagerSimple.tla** - упрощенная модель для быстрой проверки
- **PriorityManagerSimple.cfg** - конфигурация для упрощенной модели

### Документация
- **FORMAL_SPECIFICATION.md** - подробное описание формальных свойств

## Установка TLA+ Toolbox

### Linux
```bash
# Скачать с GitHub
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/TLAToolbox-1.8.0-linux.gtk.x86_64.zip
unzip TLAToolbox-1.8.0-linux.gtk.x86_64.zip
cd toolbox
./toolbox
```

### Или использовать Java напрямую
```bash
# Скачать tla2tools.jar
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Проверить модель
java -cp tla2tools.jar tlc2.TLC PriorityManagerSimple.tla -config PriorityManagerSimple.cfg
```

## Быстрый старт

### 1. Проверка упрощенной модели
```bash
java -cp tla2tools.jar tlc2.TLC PriorityManagerSimple
```

Ожидаемый результат:
```
TLC2 Version 2.18
...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = ...
States analyzed: ~1000
```

### 2. Проверка полной модели
```bash
java -cp tla2tools.jar tlc2.TLC PriorityManager
```

Это займет больше времени из-за большего пространства состояний.

## Проверяемые свойства

### Инварианты (должны быть истинны всегда)
- ✓ Приоритеты в границах [MIN_PRIORITY, MAX_PRIORITY]
- ✓ Количество процессов ≤ MAX_PROCESSES
- ✓ Приоритеты не увеличиваются при высокой нагрузке

### Свойства живости (что-то в конечном итоге произойдет)
- ✓ При перегрузке приоритеты снизятся
- ✓ Завершенные процессы будут удалены
- ✓ Система не застрянет в перегруженном состоянии

## Интерпретация результатов

### Успешная проверка
```
Model checking completed. No error has been found.
```
Все свойства выполняются для всех достижимых состояний.

### Нарушение инварианта
```
Error: Invariant PriorityInBounds is violated.
The behavior up to this point is:
State 1: ...
State 2: ...
```
TLC покажет последовательность действий, приводящую к ошибке.

### Нарушение свойства живости
```
Error: Temporal properties were violated.
```
Система может застрять в нежелательном состоянии.

## Модификация спецификации

### Изменение параметров
Отредактируйте `.cfg` файл:
```
CONSTANTS
    MAX_PROCESSES = 10    # Увеличить для большей системы
    NUM_CPUS = 8          # Количество ядер
    CRITICAL_LOAD_MULT = 1.5  # Более агрессивная корректировка
```

### Добавление нового свойства
В `.tla` файле:
```tla
\* Новое свойство: приоритет никогда не падает ниже 20
MinimumUsablePriority ==
    \A pid \in processes : priorities[pid] >= 20
```

В `.cfg` файле:
```
INVARIANTS
    MinimumUsablePriority
```

## Связь с Rust-кодом

| TLA+ действие | Rust функция |
|---------------|--------------|
| DiscoverProcess | `discover_processes()` |
| TerminateProcess | `cleanup_finished_processes()` |
| AdjustPriorityByLoad | `adjust_priorities_based_on_health()` |
| UpdateSystemState | `check_system_health()` |

## Полезные команды

### Генерация графа состояний
```bash
java -cp tla2tools.jar tlc2.TLC -dump dot states.dot PriorityManagerSimple
dot -Tpng states.dot -o states.png
```

### Проверка с трассировкой
```bash
java -cp tla2tools.jar tlc2.TLC -coverage 1 PriorityManagerSimple
```

### Симуляция (случайные трассы)
```bash
java -cp tla2tools.jar tlc2.TLC -simulate PriorityManagerSimple
```

## Дальнейшее развитие

1. Добавить модель восстановления приоритетов
2. Моделировать взаимодействие с планировщиком ОС
3. Добавить временные ограничения (real-time constraints)
4. Моделировать сетевое взаимодействие для распределенной версии
5. Добавить вероятностные свойства (PlusCal)

## Ресурсы

- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Examples](https://github.com/tlaplus/Examples)
- [Specifying Systems (книга Лэмпорта)](https://lamport.azurewebsites.net/tla/book.html)
