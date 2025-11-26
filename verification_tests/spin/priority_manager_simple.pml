/* Упрощенная SPIN модель для Priority Manager
 * Фокус на проверке основных safety и liveness свойств
 */

#define MIN_PRIORITY 10
#define MAX_PRIORITY 95
#define CRITICAL_LOAD 50
#define STEP_SIZE 10

/* Состояние */
byte prio = MAX_PRIORITY;
byte load = 0;
byte adjustments = 0;

/* Процесс: Сценарий перегрузки */
active proctype Scenario() {
    /* Увеличиваем нагрузку */
    load = 60;
    
    /* Ждем корректировок */
    do
    :: (prio > MIN_PRIORITY) -> skip;
    :: (prio == MIN_PRIORITY) -> break;
    od;
    
    /* Уменьшаем нагрузку */
    load = 0;
}

/* Процесс: Корректировка приоритета */
active proctype PriorityAdjuster() {
    do
    :: (load > CRITICAL_LOAD && prio > MIN_PRIORITY) ->
        atomic {
            if
            :: (prio >= MIN_PRIORITY + STEP_SIZE) ->
                prio = prio - STEP_SIZE;
            :: else ->
                prio = MIN_PRIORITY;
            fi;
            adjustments = adjustments + 1;
        }
    :: else -> skip;
    od
}

/* Safety свойства */

/* S1: Приоритет всегда в границах */
ltl priority_bounds {
    [](prio >= MIN_PRIORITY && prio <= MAX_PRIORITY)
}

/* S2: Монотонное уменьшение при перегрузке */
ltl monotonic_decrease {
    [](load > CRITICAL_LOAD -> (prio <= MAX_PRIORITY))
}

/* S3: Если приоритет уменьшился, он не больше предыдущего */
ltl no_increase_under_load {
    [](load > CRITICAL_LOAD -> X(prio <= MAX_PRIORITY))
}

/* Liveness свойства */

/* L1: Если перегрузка, в конечном итоге приоритет уменьшится */
ltl eventual_decrease {
    [](load > CRITICAL_LOAD -> <>(prio < MAX_PRIORITY || load <= CRITICAL_LOAD))
}

/* L2: Если перегрузка, в конечном итоге достигнем минимума */
ltl eventual_minimum {
    [](load > CRITICAL_LOAD -> <>(prio == MIN_PRIORITY || load <= CRITICAL_LOAD))
}

/* Finiteness свойства */

/* F1: Конечность корректировок */
ltl finite_adjustments {
    <>(adjustments >= 9 -> prio == MIN_PRIORITY)
}

/* F2: Система в конечном итоге стабилизируется */
ltl eventual_stability {
    <>(prio == MIN_PRIORITY || load <= CRITICAL_LOAD)
}
