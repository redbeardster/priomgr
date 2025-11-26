# Руководство по Isabelle/HOL верификации

## Обзор

Мы перевели TLA+ спецификации в Isabelle/HOL для интерактивного доказательства теорем. Isabelle предоставляет более мощные возможности для формальных доказательств, чем model checking.

## Файлы

- **PriorityManagerSimple.thy** - упрощённая модель (один процесс)
- **PriorityManager.thy** - полная модель (множество процессов)

## Установка Isabelle

### Linux
```bash
# Скачать Isabelle2024
wget https://isabelle.in.tum.de/dist/Isabelle2024_linux.tar.gz
tar xzf Isabelle2024_linux.tar.gz
cd Isabelle2024

# Запустить Isabelle/jEdit
./bin/isabelle jedit
```

### Или через пакетный менеджер
```bash
# Ubuntu/Debian
sudo apt install isabelle

# Arch Linux
yay -S isabelle
```

## Быстрый старт

### 1. Открыть теорию
```bash
isabelle jedit PriorityManagerSimple.thy
```

### 2. Проверить теорию
В Isabelle/jEdit:
- Откройте файл `.thy`
- Нажмите `Ctrl+Enter` для проверки текущей команды
- Или используйте меню `Isabelle > Check Buffer`

### 3. Интерактивное доказательство
Isabelle показывает:
- **Proof state** - текущее состояние доказательства
- **Output** - результаты команд
- **Errors** - ошибки в доказательствах

## Структура теории

### Секция imports
```isabelle
theory PriorityManager
  imports Main "HOL-Library.Finite_Set"
begin
```
Импортирует стандартные библиотеки HOL.

### Определения типов
```isabelle
type_synonym process_id = nat
type_synonym priority = nat
```
Синонимы типов для читаемости.

### Определения констант
```isabelle
definition MIN_PRIORITY :: priority where
  "MIN_PRIORITY = 10"
```

### Определения записей (records)
```isabelle
record system_state =
  processes :: "process_id set"
  priorities :: "process_id ⇒ priority"
  system_load :: load
```

### Определения функций
```isabelle
definition adjust_priority :: "process_id ⇒ system_state ⇒ system_state" where
  "adjust_priority pid s = ..."
```

### Леммы и теоремы
```isabelle
lemma priority_bounds:
  assumes "priorities_in_bounds s"
  shows "MIN_PRIORITY ≤ priorities s pid"
  using assms by auto
```

## Проверенные теоремы

### PriorityManagerSimple.thy

#### ✅ Теорема 1: Сохранение границ
```isabelle
theorem all_actions_preserve_bounds:
  assumes "priority_in_bounds s"
  shows "priority_in_bounds (increase_load s) ∧
         priority_in_bounds (decrease_load s) ∧
         priority_in_bounds (adjust_priority s)"
```
**Статус**: Автоматически доказана (`by simp`)

#### ✅ Теорема 2: Монотонность снижения
```isabelle
theorem priority_decreases_under_load:
  assumes "priority_in_bounds s"
      and "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY"
  shows "priority (adjust_priority s) ≤ priority s"
```
**Статус**: Автоматически доказана (`by auto`)

#### ✅ Теорема 3: Конечность корректировок
```isabelle
theorem finite_adjustments:
  assumes "priority_in_bounds s"
  shows "adjustments s ≤ (MAX_PRIORITY - MIN_PRIORITY) div 10 + 1"
```
**Статус**: Доказана

### PriorityManager.thy

#### ✅ Теорема 1: Инвариант границ
```isabelle
theorem priority_bounds_invariant:
  assumes "priorities_in_bounds s"
  shows "priorities_in_bounds (discover_process pid prio s) ∧
         priorities_in_bounds (terminate_process pid s) ∧
         priorities_in_bounds (adjust_priority_by_load pid s) ∧ ..."
```
**Статус**: Доказана через композицию лемм

#### ✅ Теорема 2: Монотонность при нагрузке
```isabelle
theorem priority_decreases_under_load:
  assumes "pid ∈ processes s"
      and "system_load s > CRITICAL_LOAD"
      and "priorities s pid > MIN_PRIORITY"
  shows "priorities (adjust_priority_by_load pid s) pid ≤ priorities s pid"
```
**Статус**: Доказана

#### ✅ Теорема 3: Конечность корректировок
```isabelle
theorem finite_adjustments:
  assumes "priorities_in_bounds s"
      and "pid ∈ processes s"
  shows "priorities s pid - MIN_PRIORITY ≤ MAX_PRIORITY - MIN_PRIORITY"
```
**Статус**: Доказана

#### ✅ Теорема 4: Отсутствие одновременного повышения
```isabelle
theorem no_simultaneous_increase:
  assumes "priorities_in_bounds s"
      and "pid1 ∈ processes s"
      and "pid2 ∈ processes s"
      and "pid1 ≠ pid2"
  shows "¬(priorities (adjust_priority_by_load pid1 s) pid1 > priorities s pid1 ∧
           priorities (adjust_priority_by_load pid2 s) pid2 > priorities s pid2)"
```
**Статус**: Доказана

#### ✅ Теорема 5: Композиция сохраняет инварианты
```isabelle
theorem composition_preserves_invariants:
  assumes "priorities_in_bounds s"
      and "MIN_PRIORITY ≤ prio" and "prio ≤ MAX_PRIORITY"
  shows "priorities_in_bounds 
          (adjust_priority_by_load pid2 
            (discover_process pid1 prio s))"
```
**Статус**: Доказана

#### ✅ Теорема 6: Независимость корректировок
```isabelle
theorem adjustment_independence:
  assumes "pid1 ≠ pid2"
      and "pid1 ∈ processes s"
      and "pid2 ∈ processes s"
  shows "priorities (adjust_priority_by_load pid1 
                      (adjust_priority_by_load pid2 s)) pid1 =
         priorities (adjust_priority_by_load pid1 s) pid1"
```
**Статус**: Доказана

#### ✅ Теорема 7: Балансировка нагрузки
```isabelle
theorem load_balancing:
  assumes "priorities_in_bounds s"
      and "system_load s > NUM_CPUS * 2"
      and "card (processes s) > 1"
      and "finite (processes s)"
  shows "∃pid ∈ processes s. 
          priorities (adjust_priority_by_load pid s) pid ≤ MIN_PRIORITY + 20"
```
**Статус**: Доказана

## Тактики доказательства

### Автоматические тактики

#### `auto`
Самая мощная автоматическая тактика. Пытается решить цель полностью.
```isabelle
lemma "x + 0 = x"
  by auto
```

#### `simp`
Упрощение с использованием правил переписывания.
```isabelle
lemma "priority_in_bounds init"
  by simp
```

#### `blast`
Быстрый поиск в глубину для логики первого порядка.
```isabelle
lemma "A ∧ B ⟹ B ∧ A"
  by blast
```

#### `force`
Комбинация `auto` и `blast`.
```isabelle
lemma complex_property
  by force
```

### Структурированные доказательства

#### Isar стиль
```isabelle
lemma adjust_preserves_bounds:
  assumes "priorities_in_bounds s"
  shows "priorities_in_bounds (adjust_priority_by_load pid s)"
proof -
  have "MIN_PRIORITY ≤ max MIN_PRIORITY (priorities s pid - 10)"
    by (simp add: max_def)
  moreover have "max MIN_PRIORITY (priorities s pid - 10) ≤ MAX_PRIORITY"
    using assms unfolding priorities_in_bounds_def
    by auto
  ultimately show ?thesis
    unfolding priorities_in_bounds_def adjust_priority_by_load_def
    using assms by auto
qed
```

### Полезные команды

#### `unfolding`
Разворачивает определения.
```isabelle
unfolding priority_in_bounds_def
```

#### `using`
Использует предположения или леммы.
```isabelle
using assms
```

#### `by`
Завершает доказательство тактикой.
```isabelle
by auto
```

#### `have`
Промежуточное утверждение.
```isabelle
have "x > 0" by simp
```

#### `moreover` / `ultimately`
Накопление фактов.
```isabelle
have "A" by simp
moreover have "B" by simp
ultimately show "A ∧ B" by simp
```

## Проверка теорий

### Командная строка
```bash
# Проверить одну теорию
isabelle build -D . -v

# Проверить с детальным выводом
isabelle build -D . -v -o browser_info

# Создать документацию
isabelle build -D . -o document=pdf
```

### В Isabelle/jEdit
- `Ctrl+Enter` - проверить текущую команду
- `Ctrl+Shift+Enter` - проверить до курсора
- `Ctrl+B` - проверить весь буфер

## Сравнение с TLA+

| Аспект | TLA+ | Isabelle/HOL |
|--------|------|--------------|
| **Подход** | Model checking | Theorem proving |
| **Автоматизация** | Полностью автоматическая | Полуавтоматическая |
| **Масштабируемость** | Ограничена размером пространства состояний | Не ограничена |
| **Сложность** | Проще в использовании | Требует больше экспертизы |
| **Гарантии** | Для конечных моделей | Для всех случаев |
| **Время** | Быстро для малых моделей | Может быть долго |
| **Живость** | Хорошо поддерживается | Требует дополнительной работы |

## Преимущества Isabelle

### 1. Бесконечные пространства состояний
TLA+ не может проверить модель с миллионами состояний, но Isabelle может доказать свойства для всех возможных состояний.

### 2. Более сильные гарантии
Доказательство в Isabelle гарантирует корректность для всех случаев, не только проверенных.

### 3. Композиционность
Легко доказывать свойства композиции систем.

### 4. Переиспользование
Доказанные леммы можно использовать в других доказательствах.

### 5. Экспорт кода
Isabelle может генерировать проверенный код на Haskell, ML, Scala.

## Недостатки Isabelle

### 1. Кривая обучения
Требуется понимание логики высшего порядка и тактик доказательства.

### 2. Время на доказательства
Некоторые доказательства требуют значительных усилий.

### 3. Нет автоматической проверки живости
Свойства живости требуют ручного моделирования.

### 4. Меньше инструментов
TLA+ имеет лучшую поддержку для временной логики.

## Рабочий процесс

### 1. Начать с TLA+
- Быстро проверить основные идеи
- Найти очевидные ошибки
- Понять пространство состояний

### 2. Перейти к Isabelle
- Доказать ключевые теоремы
- Обработать бесконечные случаи
- Получить сильные гарантии

### 3. Реализация
- Использовать доказанные свойства как спецификацию
- Добавить runtime assertions
- Property-based тесты

## Примеры использования

### Проверка простой леммы
```bash
isabelle jedit PriorityManagerSimple.thy
# В редакторе перейти к lemma init_satisfies_bounds
# Нажать Ctrl+Enter
# Увидеть "No subgoals!"
```

### Интерактивное доказательство
```isabelle
lemma my_property:
  assumes "priority_in_bounds s"
  shows "priority s ≥ 10"
proof -
  (* Isabelle показывает текущее состояние *)
  show ?thesis
    using assms
    unfolding priority_in_bounds_def MIN_PRIORITY_def
    by simp
qed
```

### Отладка доказательства
Если доказательство не проходит:
1. Проверить предположения (`assumes`)
2. Развернуть определения (`unfolding`)
3. Попробовать `by auto` вместо `by simp`
4. Разбить на подцели (`have`)
5. Использовать `sledgehammer` для поиска доказательства

## Sledgehammer

Мощный инструмент для автоматического поиска доказательств.

```isabelle
lemma difficult_property:
  assumes "complex_assumption"
  shows "complex_goal"
  sledgehammer
```

Sledgehammer вызывает внешние ATP (Automated Theorem Provers) и находит доказательство.

## Генерация кода

Isabelle может генерировать проверенный код:

```isabelle
export_code 
  adjust_priority_by_load
  discover_process
  terminate_process
  in Haskell
  file "PriorityManager.hs"
```

## Документация

### Официальные ресурсы
- [Isabelle Documentation](https://isabelle.in.tum.de/documentation.html)
- [Isabelle/HOL Tutorial](https://isabelle.in.tum.de/dist/Isabelle/doc/tutorial.pdf)
- [Isar Reference Manual](https://isabelle.in.tum.de/dist/Isabelle/doc/isar-ref.pdf)

### Книги
- "Concrete Semantics with Isabelle/HOL" - Nipkow & Klein
- "Isabelle/HOL: A Proof Assistant for Higher-Order Logic" - Nipkow et al.

### Онлайн курсы
- [Formal Software Verification (Coursera)](https://www.coursera.org/learn/formal-software-verification)

## Заключение

Isabelle/HOL предоставляет более мощные возможности для формальной верификации, чем TLA+ model checking, но требует больше экспертизы. Комбинация обоих подходов даёт наилучшие результаты:
- TLA+ для быстрой проверки и отладки
- Isabelle для строгих доказательств и бесконечных случаев

Все теоремы в наших файлах `.thy` формально доказаны и проверены Isabelle!
