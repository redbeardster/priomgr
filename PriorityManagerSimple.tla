---------------------- MODULE PriorityManagerSimple ----------------------
EXTENDS Integers, TLC

CONSTANTS MIN_PRIORITY, MAX_PRIORITY, CRITICAL_LOAD

VARIABLES priority, load, adjustments

vars == <<priority, load, adjustments>>

-----------------------------------------------------------------------------

Init ==
    /\ priority = MAX_PRIORITY
    /\ load = 0
    /\ adjustments = 0

IncreaseLoad ==
    /\ load < 100
    /\ load' = load + 10
    /\ UNCHANGED <<priority, adjustments>>

DecreaseLoad ==
    /\ load > 0
    /\ load' = load - 10
    /\ UNCHANGED <<priority, adjustments>>

AdjustPriority ==
    /\ load > CRITICAL_LOAD
    /\ priority > MIN_PRIORITY
    /\ priority' = IF priority - 10 < MIN_PRIORITY 
                   THEN MIN_PRIORITY 
                   ELSE priority - 10
    /\ adjustments' = adjustments + 1
    /\ UNCHANGED load

-----------------------------------------------------------------------------

Next ==
    \/ IncreaseLoad
    \/ DecreaseLoad
    \/ AdjustPriority

\* Добавляем weak fairness для AdjustPriority
\* Это гарантирует, что если корректировка возможна, она в конечном итоге произойдёт
Spec == Init /\ [][Next]_vars /\ WF_vars(AdjustPriority)

-----------------------------------------------------------------------------
\* Свойства безопасности (Safety)

PriorityInBounds ==
    /\ priority >= MIN_PRIORITY
    /\ priority <= MAX_PRIORITY

NoNegativePriority ==
    priority >= 0

MonotonicDecrease ==
    \* Приоритет только уменьшается при высокой нагрузке
    (load > CRITICAL_LOAD /\ priority > MIN_PRIORITY) =>
        (priority' <= priority)

AdjustmentsBounded ==
    \* Количество корректировок ограничено
    adjustments <= (MAX_PRIORITY - MIN_PRIORITY) \div 10 + 1

-----------------------------------------------------------------------------
\* Свойства живости (Liveness)

PriorityDecreasesUnderLoad ==
    \* При высокой нагрузке приоритет в конечном итоге уменьшится
    (load > CRITICAL_LOAD /\ priority > MIN_PRIORITY) ~> 
        (priority < MAX_PRIORITY \/ load <= CRITICAL_LOAD)

EventualMinPriority ==
    \* Если нагрузка постоянно высокая, приоритет достигнет минимума
    (load > CRITICAL_LOAD) ~> (priority = MIN_PRIORITY \/ load <= CRITICAL_LOAD)

EventualAdjustment ==
    \* Если нужна корректировка, она в конечном итоге произойдет
    (load > CRITICAL_LOAD /\ priority > MIN_PRIORITY) ~> (adjustments' > adjustments)

-----------------------------------------------------------------------------
\* Свойства композиции (Composition)

CompositionPreservesInvariants ==
    \* Последовательность действий сохраняет инварианты
    PriorityInBounds /\ PriorityInBounds' => PriorityInBounds''

IndependenceOfActions ==
    \* Изменение нагрузки не влияет на приоритет напрямую
    (IncreaseLoad \/ DecreaseLoad) => (priority' = priority)

-----------------------------------------------------------------------------
\* Свойства конечности (Finiteness)

FiniteAdjustments ==
    \* Корректировки конечны
    adjustments < 100

TerminationGuarantee ==
    \* Система достигнет стабильного состояния
    <>(priority = MIN_PRIORITY \/ load <= CRITICAL_LOAD)

=============================================================================
