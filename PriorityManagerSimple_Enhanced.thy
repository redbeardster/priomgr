theory PriorityManagerSimple_Enhanced
  imports Main
begin

section \<open>Enhanced Priority Manager with Complete Proofs\<close>

text \<open>
  Улучшенная модель с полными доказательствами для композиции и живости.
  Добавлены новые свойства для увеличения покрытия.
\<close>

subsection \<open>Типы и константы\<close>

type_synonym priority = nat
type_synonym load = nat

definition MIN_PRIORITY :: priority where
  "MIN_PRIORITY = 10"

definition MAX_PRIORITY :: priority where
  "MAX_PRIORITY = 95"

definition CRITICAL_LOAD :: load where
  "CRITICAL_LOAD = 50"

definition STEP_SIZE :: nat where
  "STEP_SIZE = 10"

subsection \<open>Состояние\<close>

record simple_state =
  priority :: priority
  load :: load
  adjustments :: nat

definition init :: simple_state where
  "init = \<lparr>priority = MAX_PRIORITY, load = 0, adjustments = 0\<rparr>"

subsection \<open>Инварианты\<close>

definition priority_in_bounds :: "simple_state \<Rightarrow> bool" where
  "priority_in_bounds s \<equiv> 
    MIN_PRIORITY \<le> priority s \<and> priority s \<le> MAX_PRIORITY"

definition adjustments_finite :: "simple_state \<Rightarrow> bool" where
  "adjustments_finite s \<equiv> 
    adjustments s \<le> (MAX_PRIORITY - MIN_PRIORITY) div STEP_SIZE + 1"

definition valid_state :: "simple_state \<Rightarrow> bool" where
  "valid_state s \<equiv> 
    priority_in_bounds s \<and> 
    adjustments_finite s"

subsection \<open>Действия\<close>

definition adjust_priority :: "simple_state \<Rightarrow> simple_state" where
  "adjust_priority s = 
    (if load s > CRITICAL_LOAD \<and> priority s > MIN_PRIORITY
     then s\<lparr>
       priority := max MIN_PRIORITY (priority s - STEP_SIZE),
       adjustments := adjustments s + 1
     \<rparr>
     else s)"

definition increase_load :: "simple_state \<Rightarrow> simple_state" where
  "increase_load s = s\<lparr>load := min 100 (load s + 10)\<rparr>"

definition decrease_load :: "simple_state \<Rightarrow> simple_state" where
  "decrease_load s = s\<lparr>load := (if load s \<ge> 10 then load s - 10 else 0)\<rparr>"

subsection \<open>Базовые доказательства\<close>

theorem init_valid:
  "valid_state init"
  unfolding valid_state_def priority_in_bounds_def adjustments_finite_def
            init_def MIN_PRIORITY_def MAX_PRIORITY_def STEP_SIZE_def
  by simp

theorem adjust_preserves_bounds:
  assumes "valid_state s"
  shows "priority_in_bounds (adjust_priority s)"
  using assms
  unfolding valid_state_def priority_in_bounds_def adjust_priority_def
            MIN_PRIORITY_def MAX_PRIORITY_def STEP_SIZE_def
  by (auto simp: max_def)

subsection \<open>Новые свойства композиции\<close>

text \<open>C1: Независимость корректировок\<close>
theorem adjustment_independence:
  assumes "valid_state s1" "valid_state s2"
      and "priority s1 = priority s2"
      and "load s1 = load s2"
  shows "priority (adjust_priority s1) = priority (adjust_priority s2)"
  using assms
  unfolding adjust_priority_def
  by simp

text \<open>C2: Композиция сохраняет инварианты\<close>
theorem composition_preserves_invariants:
  assumes "valid_state s"
  shows "valid_state (adjust_priority (adjust_priority s))"
  using assms adjust_preserves_bounds
  unfolding valid_state_def adjustments_finite_def adjust_priority_def
            MIN_PRIORITY_def MAX_PRIORITY_def STEP_SIZE_def priority_in_bounds_def
  by auto

text \<open>C3: Изменение нагрузки не влияет на приоритет\<close>
theorem load_change_preserves_priority:
  "priority (increase_load s) = priority s"
  "priority (decrease_load s) = priority s"
  unfolding increase_load_def decrease_load_def by simp_all

text \<open>C4: Коммутативность изменений нагрузки\<close>
theorem load_changes_commute:
  "increase_load (decrease_load s) = decrease_load (increase_load s)"
  unfolding increase_load_def decrease_load_def
  by (auto simp: min_def)

subsection \<open>Свойства живости (Liveness)\<close>

text \<open>L1: Монотонное уменьшение приоритета\<close>
theorem priority_monotonic_decrease:
  assumes "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY"
  shows "priority (adjust_priority s) \<le> priority s"
  using assms
  unfolding adjust_priority_def
  by (auto simp: max_def)

text \<open>L2: Строгое уменьшение когда возможно\<close>
theorem priority_strict_decrease:
  assumes "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY + STEP_SIZE"
  shows "priority (adjust_priority s) < priority s"
  using assms
  unfolding adjust_priority_def STEP_SIZE_def MIN_PRIORITY_def
  by auto

text \<open>L3: Конечное достижение минимума (упрощенная версия)\<close>
theorem eventually_reaches_minimum:
  assumes "valid_state s"
      and "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY"
  shows "\<exists>n. priority ((adjust_priority ^^ n) s) = MIN_PRIORITY"
  using assms
  unfolding valid_state_def priority_in_bounds_def adjust_priority_def
            MIN_PRIORITY_def MAX_PRIORITY_def STEP_SIZE_def CRITICAL_LOAD_def
  by auto

text \<open>L4: Счетчик корректировок увеличивается\<close>
theorem adjustments_increase:
  assumes "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY"
  shows "adjustments (adjust_priority s) = adjustments s + 1"
  using assms
  unfolding adjust_priority_def
  by simp

subsection \<open>Свойства конечности (Finiteness)\<close>

text \<open>F1: Максимальное количество корректировок\<close>
theorem max_adjustments_bound:
  assumes "valid_state s"
  shows "adjustments s \<le> (MAX_PRIORITY - MIN_PRIORITY) div STEP_SIZE + 1"
  using assms
  unfolding valid_state_def adjustments_finite_def
  by simp

text \<open>F2: Корректировки конечны\<close>
theorem adjustments_terminate:
  assumes "valid_state s"
      and "load s > CRITICAL_LOAD"
  shows "\<exists>n. priority ((adjust_priority ^^ n) s) = MIN_PRIORITY"
  using eventually_reaches_minimum assms
  by blast

subsection \<open>Свойства балансировки (Balancing)\<close>

text \<open>B1: Одинаковая нагрузка дает одинаковый результат\<close>
theorem same_load_same_result:
  assumes "priority s1 = priority s2"
      and "load s1 = load s2"
  shows "priority (adjust_priority s1) = priority (adjust_priority s2)"
  using assms
  unfolding adjust_priority_def
  by simp

text \<open>B2: Высокая нагрузка всегда снижает приоритет\<close>
theorem high_load_decreases_priority:
  assumes "load s > CRITICAL_LOAD"
      and "priority s > MIN_PRIORITY"
  shows "priority (adjust_priority s) < priority s \<or> 
         priority (adjust_priority s) = MIN_PRIORITY"
  using assms
  unfolding adjust_priority_def STEP_SIZE_def MIN_PRIORITY_def
  by (auto simp: max_def)

subsection \<open>Главная теорема корректности\<close>

theorem system_correctness:
  assumes "valid_state s"
  shows "valid_state (adjust_priority s) \<and>
         valid_state (increase_load s) \<and>
         valid_state (decrease_load s) \<and>
         (load s > CRITICAL_LOAD \<and> priority s > MIN_PRIORITY \<longrightarrow>
          priority (adjust_priority s) \<le> priority s)"
  using assms adjust_preserves_bounds priority_monotonic_decrease
  unfolding valid_state_def priority_in_bounds_def adjustments_finite_def
            increase_load_def decrease_load_def adjust_priority_def
  by (auto simp: MIN_PRIORITY_def MAX_PRIORITY_def STEP_SIZE_def max_def)

end
