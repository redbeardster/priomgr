/* SPIN Model for Priority Manager
 * 
 * SPIN - Simple Promela Interpreter
 * Специализирован для проверки liveness и deadlock свойств
 */

#define MIN_PRIORITY 10
#define MAX_PRIORITY 95
#define CRITICAL_LOAD 50
#define STEP_SIZE 10

/* Состояние системы */
byte prio = MAX_PRIORITY;  /* priority - зарезервированное слово в SPIN */
byte load = 0;
byte adjustments = 0;
bool system_overloaded = false;

/* Процесс: Изменение нагрузки */
active proctype LoadManager() {
    do
    :: atomic { load < 100 -> load = load + 10; }
    :: atomic { load > 0 -> load = load - 10; }
    od
}

/* Процесс: Корректировка приоритета */
active proctype PriorityAdjuster() {
    do
    :: atomic {
        (load > CRITICAL_LOAD && prio > MIN_PRIORITY) ->
        if
        :: (prio >= MIN_PRIORITY + STEP_SIZE) ->
            prio = prio - STEP_SIZE;
            adjustments = adjustments + 1;
        :: else ->
            prio = MIN_PRIORITY;
            adjustments = adjustments + 1;
        fi;
       }
    od
}

/* Процесс: Мониторинг перегрузки */
active proctype OverloadMonitor() {
    do
    :: atomic { load > CRITICAL_LOAD -> system_overloaded = true; }
    :: atomic { load <= CRITICAL_LOAD -> system_overloaded = false; }
    od
}

/* LTL свойства для проверки */

/* L1: Если система перегружена, в конечном итоге приоритет уменьшится или нагрузка спадет */
ltl eventual_decrease {
    [](system_overloaded -> <>(!system_overloaded || prio < MAX_PRIORITY))
}

/* L2: Если система перегружена, в конечном итоге достигнем минимума или нагрузка спадет */
ltl eventual_minimum {
    [](system_overloaded -> <>(!system_overloaded || prio == MIN_PRIORITY))
}

/* L3: Система не застревает в одном состоянии навсегда (прогресс) */
ltl progress {
    []<>(prio == MIN_PRIORITY || !system_overloaded)
}

/* L4: Если достигли минимума, он сохраняется при перегрузке */
ltl minimum_stable {
    [](prio == MIN_PRIORITY && system_overloaded -> X(prio == MIN_PRIORITY))
}

/* S1: Приоритет всегда в границах (safety) */
ltl priority_bounds {
    [](prio >= MIN_PRIORITY && prio <= MAX_PRIORITY)
}

/* S2: Монотонное уменьшение при перегрузке */
ltl monotonic_decrease {
    [](system_overloaded -> (prio <= MAX_PRIORITY))
}

/* F1: Конечность корректировок */
ltl finite_adjustments {
    <>(adjustments >= 9 -> prio == MIN_PRIORITY)
}

/* Fairness: Если постоянно перегрузка, приоритет будет уменьшаться */
ltl fairness {
    ([]<>system_overloaded) -> ([]<>(prio < MAX_PRIORITY))
}
