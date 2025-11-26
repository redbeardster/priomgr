theory PriorityManager
  imports Main "HOL-Library.FSet"
begin

section ‹Priority Manager Formal Verification with Strong Typing›

subsection ‹Сильно типизированные базовые типы›

type_synonym process_id = nat

typedef priority_type = "{n::nat. n ≥ 10 ∧ n ≤ 95}"
  morphisms priority_val mk_priority
proof -
  show "∃x. x ∈ {n::nat. n ≥ 10 ∧ n ≤ 95}"
    by (rule exI[of _ 10]) simp
qed

typedef load_type = "{n::nat. n ≤ 100}"
  morphisms load_val mk_load  
proof -
  show "∃x. x ∈ {n::nat. n ≤ 100}"
    by (rule exI[of _ 0]) simp
qed

typedef memory_type = "{n::nat. n ≤ 16384}"
  morphisms memory_val mk_memory
proof -
  show "∃x. x ∈ {n::nat. n ≤ 16384}"
    by (rule exI[of _ 0]) simp
qed

setup_lifting type_definition_priority_type
setup_lifting type_definition_load_type  
setup_lifting type_definition_memory_type


definition MIN_PRIORITY :: priority_type where
  "MIN_PRIORITY = mk_priority 10"

definition MAX_PRIORITY :: priority_type where
  "MAX_PRIORITY = mk_priority 95"

definition CRITICAL_LOAD :: load_type where
  "CRITICAL_LOAD = mk_load 50"

definition NUM_CPUS :: nat where
  "NUM_CPUS = 8"


lemma MIN_PRIORITY_val [simp]: "priority_val MIN_PRIORITY = 10"
  unfolding MIN_PRIORITY_def  
  using mk_priority_inverse by auto

lemma MAX_PRIORITY_val [simp]: "priority_val MAX_PRIORITY = 95"
  unfolding MAX_PRIORITY_def
  by (simp add: mk_priority_inverse)

lemma CRITICAL_LOAD_val [simp]: "load_val CRITICAL_LOAD = 50"
  unfolding CRITICAL_LOAD_def
  using mk_load_inverse by auto


lemma priority_bounds [simp]:
  "10 ≤ priority_val p ∧ priority_val p ≤ 95"
  using priority_val by auto

lemma load_bounds [simp]:
  "load_val l ≤ 100"
  using load_val by auto

lemma memory_bounds [simp]:
  "memory_val m ≤ 16384"
  using memory_val by auto

subsection ‹Безопасные операции над типами›

lift_definition decrease_priority :: "priority_type ⇒ priority_type" is
  "λx. if x > 10 then max 10 (x - 10) else 10"
  by auto

lift_definition decrease_priority_small :: "priority_type ⇒ priority_type" is
  "λx. if x > 10 then max 10 (x - 5) else 10"  
  by auto

lift_definition decrease_priority_minimal :: "priority_type ⇒ priority_type" is
  "λx. if x > 10 then max 10 (x - 3) else 10"
  by auto


lemma decrease_priority_eq:
  "priority_val (decrease_priority p) = 
   (if priority_val p > 10 then max 10 (priority_val p - 10) else 10)"
  by transfer auto

lemma decrease_priority_small_eq:
  "priority_val (decrease_priority_small p) = 
   (if priority_val p > 10 then max 10 (priority_val p - 5) else 10)"
  by transfer auto

lemma decrease_priority_minimal_eq:
  "priority_val (decrease_priority_minimal p) = 
   (if priority_val p > 10 then max 10 (priority_val p - 3) else 10)"
  by transfer auto

subsection ‹Состояние системы›

record system_state =
  processes :: "process_id set"
  priorities :: "process_id ⇒ priority_type" 
  system_load :: load_type
  available_memory :: memory_type  
  responsiveness :: nat
  adjustment_count :: nat

text ‹Начальное состояние›
definition init_state :: system_state where
  "init_state = ⦇
    processes = {},
    priorities = (λ_. MIN_PRIORITY),
    system_load = mk_load 0,
    available_memory = mk_memory 8192,
    responsiveness = 10,
    adjustment_count = 0
  ⦈"

subsection ‹Упрощённые инварианты›

text ‹Инвариант 1: Приоритеты в границах (теперь гарантирован типом!)›
definition priorities_in_bounds :: "system_state ⇒ bool" where
  "priorities_in_bounds s ≡ True"

text ‹Инвариант 2: Количество процессов ограничено›
definition process_count_bounded :: "nat ⇒ system_state ⇒ bool" where
  "process_count_bounded max_procs s ≡ 
    finite (processes s) ∧ card (processes s) ≤ max_procs"

text ‹Инвариант 3: Нагрузка в пределах (гарантирован типом!)›  
definition load_bounded :: "system_state ⇒ bool" where
  "load_bounded s ≡ True"

text ‹Инвариант 4: Память в пределах (гарантирован типом!)›
definition memory_valid :: "system_state ⇒ bool" where
  "memory_valid s ≡ True"

text ‹Общий инвариант›
definition type_ok :: "nat ⇒ system_state ⇒ bool" where
  "type_ok max_procs s ≡
    process_count_bounded max_procs s"

subsection ‹Действия системы›

definition discover_process :: "process_id ⇒ priority_type ⇒ system_state ⇒ system_state" where
  "discover_process pid prio s = s⦇
    processes := processes s ∪ {pid},
    priorities := (priorities s)(pid := prio)
  ⦈"

definition terminate_process :: "process_id ⇒ system_state ⇒ system_state" where  
  "terminate_process pid s = s⦇
    processes := processes s - {pid}
  ⦈"

definition adjust_priority_by_load :: "process_id ⇒ system_state ⇒ system_state" where
  "adjust_priority_by_load pid s = 
    (if pid ∈ processes s ∧ load_val (system_load s) > 50
     then s⦇
       priorities := (priorities s)(pid := decrease_priority (priorities s pid)),
       adjustment_count := adjustment_count s + 1
     ⦈
     else s)"

definition adjust_priority_by_responsiveness :: "process_id ⇒ system_state ⇒ system_state" where
  "adjust_priority_by_responsiveness pid s = 
    (if pid ∈ processes s ∧ responsiveness s > 2000
     then s⦇
       priorities := (priorities s)(pid := decrease_priority_small (priorities s pid)),
       adjustment_count := adjustment_count s + 1
     ⦈
     else s)"

definition adjust_priority_by_memory :: "process_id ⇒ system_state ⇒ system_state" where
  "adjust_priority_by_memory pid s = 
    (if pid ∈ processes s ∧ memory_val (available_memory s) < 100
     then s⦇
       priorities := (priorities s)(pid := decrease_priority_minimal (priorities s pid)),
       adjustment_count := adjustment_count s + 1
     ⦈
     else s)"

subsection ‹Упрощённые доказательства›

text ‹Начальное состояние корректно›
lemma init_state_type_ok:
  "type_ok max_procs init_state"
  unfolding type_ok_def process_count_bounded_def init_state_def
  by auto

text ‹Все действия сохраняют границы приоритетов (теперь тривиально!)›
lemma discover_process_preserves_bounds:
  "priorities_in_bounds (discover_process pid prio s)"
  unfolding priorities_in_bounds_def by simp

lemma terminate_process_preserves_bounds:
  "priorities_in_bounds (terminate_process pid s)"  
  unfolding priorities_in_bounds_def by simp

lemma adjust_by_load_preserves_bounds:
  "priorities_in_bounds (adjust_priority_by_load pid s)"
  unfolding priorities_in_bounds_def by simp

lemma adjust_by_responsiveness_preserves_bounds:
  "priorities_in_bounds (adjust_priority_by_responsiveness pid s)"
  unfolding priorities_in_bounds_def by simp

lemma adjust_by_memory_preserves_bounds:
  "priorities_in_bounds (adjust_priority_by_memory pid s)"
  unfolding priorities_in_bounds_def by simp

text ‹Главная теорема сохранения инвариантов›
theorem priority_bounds_invariant:
  "priorities_in_bounds (discover_process pid prio s) ∧
   priorities_in_bounds (terminate_process pid s) ∧
   priorities_in_bounds (adjust_priority_by_load pid s) ∧
   priorities_in_bounds (adjust_priority_by_responsiveness pid s) ∧
   priorities_in_bounds (adjust_priority_by_memory pid s)"
  by (simp add: priorities_in_bounds_def)

subsection ‹Свойства значений (value-level proofs)›

text ‹Приоритет уменьшается при высокой нагрузке›
theorem priority_decreases_under_load:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
      and "priority_val (priorities s pid) > 10"
    shows "priority_val (priorities (adjust_priority_by_load pid s) pid) < 
           priority_val (priorities s pid)"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid s) pid) = 
        priority_val (decrease_priority (priorities s pid))"
    using assms unfolding adjust_priority_by_load_def by simp
  
  also have "... = (if priority_val (priorities s pid) > 10 then 
                   max 10 (priority_val (priorities s pid) - 10) else 10)"
    by (simp add: decrease_priority_eq)
  
  also have "... < priority_val (priorities s pid)"
    using assms(3) by auto
    
  finally show ?thesis .
qed

text ‹Строгое уменьшение когда возможно›
lemma priority_strictly_decreases:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50" 
      and "priority_val (priorities s pid) > 20"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) <
         priority_val (priorities s pid)"
  unfolding adjust_priority_by_load_def decrease_priority_eq
  using assms 
  using adjust_priority_by_load_def priority_decreases_under_load by auto

text ‹Счётчик корректировок увеличивается›
lemma adjustment_increments_counter:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
    shows "adjustment_count (adjust_priority_by_load pid s) = 
           adjustment_count s + 1"
  unfolding adjust_priority_by_load_def
  using assms by auto

subsection ‹Свойства прогресса›

text ‹Прогресс к минимальному приоритету›
lemma progress_towards_min_priority:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
      and "priority_val (priorities s pid) > 10"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) ≤
         priority_val (priorities s pid)"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid s) pid) = 
        max 10 (priority_val (priorities s pid) - 10)"
    using assms
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  then show ?thesis
    by (simp add: max_def)
qed


(* Дополнительные леммы *)

subsection ‹Точные свойства корректировки приоритетов›

text ‹Точное уменьшение когда возможно›
lemma exact_decrease_when_possible:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
      and "priority_val (priorities s pid) > 20"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) =
         priority_val (priorities s pid) - 10"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid s) pid) = 
        max 10 (priority_val (priorities s pid) - 10)"
    using assms
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  with assms(3) show ?thesis
    by (simp add: max_def)
qed

text ‹Гарантированное не-увеличение›
lemma never_increases:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) ≤
         priority_val (priorities s pid)"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid s) pid) = 
        max 10 (priority_val (priorities s pid) - 10)"
    using assms
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  then show ?thesis
    by (simp add: max_def)
qed

text ‹Достижение минимума›
lemma reaches_minimum:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50" 
      and "priority_val (priorities s pid) ≤ 20"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) = 10"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid s) pid) = 
        max 10 (priority_val (priorities s pid) - 10)"
    using assms
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  with assms(3) show ?thesis
  by auto
qed

text ‹Строгое уменьшение при достаточном запасе›
lemma strictly_decreases_when_possible:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50"
      and "priority_val (priorities s pid) > 20"
  shows "priority_val (priorities (adjust_priority_by_load pid s) pid) <
         priority_val (priorities s pid)"
  using assms exact_decrease_when_possible
  by simp

text ‹Монотонность по отношению к исходному приоритету›
lemma adjustment_monotonic:
  assumes "pid1 ∈ processes s" "pid2 ∈ processes s"
      and "load_val (system_load s) > 50"
      and "priority_val (priorities s pid1) ≤ priority_val (priorities s pid2)"
  shows "priority_val (priorities (adjust_priority_by_load pid1 s) pid1) ≤
         priority_val (priorities (adjust_priority_by_load pid2 s) pid2)"
proof -
  have "priority_val (priorities (adjust_priority_by_load pid1 s) pid1) = 
        max 10 (priority_val (priorities s pid1) - 10)"
    using assms(1,3)
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  also have "priority_val (priorities (adjust_priority_by_load pid2 s) pid2) = 
             max 10 (priority_val (priorities s pid2) - 10)"
    using assms(2,3)
    by (simp add: adjust_priority_by_load_def decrease_priority_eq)
  
  finally show ?thesis
    using assms(4)   by (simp add: ‹priority_val (priorities (adjust_priority_by_load pid2 s) pid2) = max 10 (priority_val (priorities s pid2) - 10)› calculation diff_le_mono)
qed

(**)


text ‹Конечное достижение минимума›
theorem eventually_reaches_min_priority:
  assumes "pid ∈ processes s"
      and "load_val (system_load s) > 50" 
      and "priority_val (priorities s pid) > 10"
  shows "∃n. n ≤ (priority_val (priorities s pid) - 10) div 10 + 1 ∧
         priority_val (priorities ((adjust_priority_by_load pid ^^ n) s) pid) = 10"
  oops 


subsection ‹Композиционные свойства›

text ‹Независимость корректировок разных процессов›
theorem adjustment_independence:
  assumes "pid1 ≠ pid2"
      and "pid1 ∈ processes s" 
      and "pid2 ∈ processes s"
  shows "priorities (adjust_priority_by_load pid1 
                      (adjust_priority_by_load pid2 s)) pid1 =
         priorities (adjust_priority_by_load pid1 s) pid1"
  unfolding adjust_priority_by_load_def
  using assms by auto

text ‹Коммутативность для разных процессов›  
 text ‹Коммутативность для разных процессов›  
theorem adjustment_commutativity:
  assumes "pid1 ≠ pid2"
      and "pid1 ∈ processes s"
      and "pid2 ∈ processes s" 
  shows "adjust_priority_by_load pid1 (adjust_priority_by_load pid2 s) =
         adjust_priority_by_load pid2 (adjust_priority_by_load pid1 s)"
  unfolding adjust_priority_by_load_def
  using assms
  by (auto simp: fun_upd_twist)

subsection ‹Метатеоремы›

text ‹Все действия сохраняют тип системы›
theorem all_actions_preserve_type:
  assumes "type_ok max_procs s"
      and "card (processes s) < max_procs" 
    shows "type_ok max_procs (discover_process pid prio s) ∧
           type_ok max_procs (terminate_process pid s) ∧  
           type_ok max_procs (adjust_priority_by_load pid s) ∧
           type_ok max_procs (adjust_priority_by_responsiveness pid s) ∧
           type_ok max_procs (adjust_priority_by_memory pid s)"
  using assms
  unfolding type_ok_def process_count_bounded_def
            discover_process_def terminate_process_def
            adjust_priority_by_load_def adjust_priority_by_responsiveness_def
            adjust_priority_by_memory_def
  by (auto simp: card_insert_if)

end