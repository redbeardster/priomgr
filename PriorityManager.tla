--------------------------- MODULE PriorityManager ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    MAX_PROCESSES,      \* Максимальное количество процессов
    MIN_PRIORITY,       \* Минимальный приоритет RT (10)
    MAX_PRIORITY,       \* Максимальный приоритет RT (95)
    NUM_CPUS,           \* Количество CPU ядер
    CRITICAL_LOAD_MULT  \* Множитель критической нагрузки (2.0)

VARIABLES
    processes,          \* Множество отслеживаемых процессов
    priorities,         \* Функция: процесс -> текущий приоритет
    system_load,        \* Текущая нагрузка системы
    available_memory,   \* Доступная память (MB)
    responsiveness,     \* Время отклика системы (ms)
    adjustment_count    \* Счетчик корректировок приоритетов

vars == <<processes, priorities, system_load, available_memory, 
          responsiveness, adjustment_count>>

ProcessIds == 1..MAX_PROCESSES

-----------------------------------------------------------------------------

TypeOK ==
    /\ processes \subseteq ProcessIds
    /\ priorities \in [processes -> MIN_PRIORITY..MAX_PRIORITY]
    /\ system_load \in 0..100
    /\ available_memory \in 0..16384  \* 0-16GB
    /\ responsiveness \in 0..10000    \* 0-10 секунд в ms
    /\ adjustment_count \in Nat

\* Ограничение пространства состояний для ускорения проверки
StateConstraint ==
    /\ adjustment_count < 3
    /\ Cardinality(processes) <= 1
    /\ system_load <= 20
    /\ responsiveness <= 3000

-----------------------------------------------------------------------------

Init ==
    /\ processes = {}
    /\ priorities = [p \in {} |-> MIN_PRIORITY]
    /\ system_load = 0
    /\ available_memory = 8192  \* 8GB
    /\ responsiveness = 10      \* 10ms
    /\ adjustment_count = 0

-----------------------------------------------------------------------------
\* Действия системы

\* Обнаружение нового процесса
DiscoverProcess(pid, initial_priority) ==
    /\ pid \notin processes
    /\ Cardinality(processes) < MAX_PROCESSES
    /\ initial_priority \in MIN_PRIORITY..MAX_PRIORITY
    /\ processes' = processes \union {pid}
    /\ priorities' = priorities @@ (pid :> initial_priority)
    /\ UNCHANGED <<system_load, available_memory, responsiveness, adjustment_count>>

\* Завершение процесса
TerminateProcess(pid) ==
    /\ pid \in processes
    /\ processes' = processes \ {pid}
    /\ priorities' = [p \in processes' |-> priorities[p]]
    /\ UNCHANGED <<system_load, available_memory, responsiveness, adjustment_count>>

\* Изменение состояния системы
UpdateSystemState ==
    /\ system_load' \in 0..100
    /\ available_memory' \in 0..16384
    /\ responsiveness' \in 0..10000
    /\ UNCHANGED <<processes, priorities, adjustment_count>>

\* Корректировка приоритета на основе нагрузки системы
AdjustPriorityByLoad(pid) ==
    /\ pid \in processes
    /\ system_load > NUM_CPUS * CRITICAL_LOAD_MULT
    /\ LET old_priority == priorities[pid]
           new_priority == IF old_priority - 10 < MIN_PRIORITY 
                          THEN MIN_PRIORITY 
                          ELSE old_priority - 10
       IN /\ priorities' = [priorities EXCEPT ![pid] = new_priority]
          /\ adjustment_count' = adjustment_count + 1
    /\ UNCHANGED <<processes, system_load, available_memory, responsiveness>>

\* Корректировка приоритета на основе отклика системы
AdjustPriorityByResponsiveness(pid) ==
    /\ pid \in processes
    /\ responsiveness > 2000  \* Порог 2 секунды
    /\ LET old_priority == priorities[pid]
           new_priority == IF old_priority - 5 < MIN_PRIORITY 
                          THEN MIN_PRIORITY 
                          ELSE old_priority - 5
       IN /\ priorities' = [priorities EXCEPT ![pid] = new_priority]
          /\ adjustment_count' = adjustment_count + 1
    /\ UNCHANGED <<processes, system_load, available_memory, responsiveness>>

\* Корректировка приоритета на основе памяти
AdjustPriorityByMemory(pid) ==
    /\ pid \in processes
    /\ available_memory < 100  \* Меньше 100MB
    /\ LET old_priority == priorities[pid]
           new_priority == IF old_priority - 3 < MIN_PRIORITY 
                          THEN MIN_PRIORITY 
                          ELSE old_priority - 3
       IN /\ priorities' = [priorities EXCEPT ![pid] = new_priority]
          /\ adjustment_count' = adjustment_count + 1
    /\ UNCHANGED <<processes, system_load, available_memory, responsiveness>>

-----------------------------------------------------------------------------

Next ==
    \/ \E pid \in ProcessIds, prio \in MIN_PRIORITY..MAX_PRIORITY : 
        DiscoverProcess(pid, prio)
    \/ \E pid \in processes : TerminateProcess(pid)
    \/ UpdateSystemState
    \/ \E pid \in processes : AdjustPriorityByLoad(pid)
    \/ \E pid \in processes : AdjustPriorityByResponsiveness(pid)
    \/ \E pid \in processes : AdjustPriorityByMemory(pid)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* ИНВАРИАНТЫ (свойства безопасности)

\* Все приоритеты в допустимых границах
PrioritiesInBounds ==
    \A pid \in processes : 
        /\ priorities[pid] >= MIN_PRIORITY
        /\ priorities[pid] <= MAX_PRIORITY

\* Приоритеты никогда не увеличиваются при высокой нагрузке
NoPriorityIncreaseUnderLoad ==
    system_load > NUM_CPUS * CRITICAL_LOAD_MULT =>
        [][\A pid \in processes : priorities'[pid] <= priorities[pid]]_vars

\* Количество процессов не превышает максимум
ProcessCountBounded ==
    Cardinality(processes) <= MAX_PROCESSES

\* Приоритеты монотонно не возрастают при проблемах
MonotonicPriorityDecrease ==
    (system_load > NUM_CPUS * CRITICAL_LOAD_MULT \/ 
     responsiveness > 2000 \/ 
     available_memory < 100) =>
        [][\A pid \in processes : priorities'[pid] <= priorities[pid]]_vars

-----------------------------------------------------------------------------
\* СВОЙСТВА ЖИВОСТИ

\* Если система перегружена, приоритеты в конечном итоге снизятся
EventualPriorityReduction ==
    (system_load > NUM_CPUS * CRITICAL_LOAD_MULT /\ processes # {}) ~>
        (\E pid \in processes : priorities[pid] = MIN_PRIORITY)

\* Завершенные процессы в конечном итоге удаляются
\* (Упрощённая версия - если процесс был, он может исчезнуть)
EventualCleanup ==
    \A pid \in ProcessIds : 
        (pid \in processes) => <>(pid \notin processes)

-----------------------------------------------------------------------------
\* ВРЕМЕННЫЕ СВОЙСТВА

\* Система не застревает в состоянии с высокой нагрузкой
NoStarvation ==
    []<>(system_load <= NUM_CPUS * CRITICAL_LOAD_MULT)

\* Приоритеты корректируются бесконечно часто при проблемах
InfiniteAdjustments ==
    (system_load > NUM_CPUS * CRITICAL_LOAD_MULT) ~> 
        (adjustment_count > 0)

-----------------------------------------------------------------------------
\* ДОПОЛНИТЕЛЬНЫЕ ПРОВЕРКИ

\* Нет одновременного повышения всех приоритетов
NoSimultaneousPriorityIncrease ==
    ~(\E pid1, pid2 \in processes : 
        pid1 # pid2 /\ 
        priorities'[pid1] > priorities[pid1] /\
        priorities'[pid2] > priorities[pid2])

\* При критической нагрузке хотя бы один процесс имеет низкий приоритет
LoadBalancing ==
    (system_load > NUM_CPUS * CRITICAL_LOAD_MULT /\ Cardinality(processes) > 1) =>
        \E pid \in processes : priorities[pid] <= MIN_PRIORITY + 20

=============================================================================
