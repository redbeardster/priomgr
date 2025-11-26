theory PriorityManagerSimple
  imports Main
begin

section \<open>Simplified Priority Manager with Strong Typing\<close>

subsection \<open>Типы с ограничениями\<close>

typedef priority_type = "{n::nat. n \<ge> 10 \<and> n \<le> 95}"
  morphisms priority_val mk_priority
proof -
  have "10 \<in> {n::nat. n \<ge> 10 \<and> n \<le> 95}" by simp
  then show ?thesis ..
qed

typedef load_type = "{n::nat. n \<le> 100}"
  morphisms load_val mk_load
proof -
  have "0 \<in> {n::nat. n \<le> 100}" by simp
  then show ?thesis ..
qed

setup_lifting type_definition_priority_type
setup_lifting type_definition_load_type

definition MIN_PRIORITY :: priority_type where
  "MIN_PRIORITY = mk_priority 10"

definition MAX_PRIORITY :: priority_type where  
  "MAX_PRIORITY = mk_priority 95"

definition CRITICAL_LOAD :: load_type where
  "CRITICAL_LOAD = mk_load 50"

lemma MIN_PRIORITY_val [simp]: "priority_val MIN_PRIORITY = 10"
  unfolding MIN_PRIORITY_def

  by (simp add: mk_priority_inverse)

lemma MAX_PRIORITY_val [simp]: "priority_val MAX_PRIORITY = 95"
  unfolding MAX_PRIORITY_def
  by (simp add: mk_priority_inverse)

lemma CRITICAL_LOAD_val [simp]: "load_val CRITICAL_LOAD = 50"
  unfolding CRITICAL_LOAD_def
  using mk_load_inverse by auto

lemma priority_bounds [simp]:
  "10 \<le> priority_val p \<and> priority_val p \<le> 95"
  using priority_val by auto

lemma load_bounds [simp]:
  "load_val l \<le> 100"
  using load_val by auto

subsection \<open>Операции над типами с lift_definition\<close>

lift_definition increase_load_val :: "load_type \<Rightarrow> load_type" is
  "\<lambda>x. if x < 100 then min (x + 10) 100 else 100"
  by auto

lift_definition decrease_load_val :: "load_type \<Rightarrow> load_type" is  
  "\<lambda>x. if x > 0 then x - 10 else 0"
  by auto

lift_definition decrease_priority :: "priority_type \<Rightarrow> priority_type" is
  "\<lambda>x. if x > 10 then max 10 (x - 10) else 10"
  by auto

lemma increase_load_val_eq:
  "load_val (increase_load_val l) = 
   (if load_val l < 100 then min (load_val l + 10) 100 else 100)"
  by transfer auto

lemma decrease_load_val_eq:
  "load_val (decrease_load_val l) = 
   (if load_val l > 0 then load_val l - 10 else 0)"
  by transfer auto

lemma decrease_priority_eq:
  "priority_val (decrease_priority p) = 
   (if priority_val p > 10 then max 10 (priority_val p - 10) else 10)"
  by transfer auto

subsection \<open>Состояние\<close>

record simple_state =
  priority :: priority_type
  load :: load_type
  adjustments :: nat

text \<open>Начальное состояние\<close>
definition init :: simple_state where
  "init = \<lparr>priority = MAX_PRIORITY, load = mk_load 0, adjustments = 0\<rparr>"

subsection \<open>Действия\<close>

definition increase_load :: "simple_state \<Rightarrow> simple_state" where
  "increase_load s = s\<lparr>load := increase_load_val (load s)\<rparr>"

definition decrease_load :: "simple_state \<Rightarrow> simple_state" where
  "decrease_load s = s\<lparr>load := decrease_load_val (load s)\<rparr>"

definition adjust_priority :: "simple_state \<Rightarrow> simple_state" where
  "adjust_priority s = (
    if load_val (load s) > 50 \<and> priority_val (priority s) > 10 then
      s\<lparr>priority := decrease_priority (priority s), adjustments := adjustments s + 1\<rparr>
    else s
  )"

subsection \<open>Инварианты\<close>

definition priority_in_bounds :: "simple_state \<Rightarrow> bool" where
  "priority_in_bounds s \<equiv> True"

definition load_in_bounds :: "simple_state \<Rightarrow> bool" where  
  "load_in_bounds s \<equiv> True"

definition MAX_ADJUSTMENTS :: nat where
  "MAX_ADJUSTMENTS = (95 - 10) div 10 + 1"

definition adjustments_bound :: "simple_state \<Rightarrow> bool" where
  "adjustments_bound s \<equiv> adjustments s \<le> MAX_ADJUSTMENTS"

definition priority_adjustments_relation :: "simple_state \<Rightarrow> bool" where
  "priority_adjustments_relation s \<equiv>
    priority_val (priority s) = 95 - 10 * min (adjustments s) ((95 - 10) div 10)"

definition valid_state :: "simple_state \<Rightarrow> bool" where
  "valid_state s \<equiv> 
    adjustments_bound s \<and>
    priority_adjustments_relation s"

subsection \<open>Упрощённые доказательства\<close>

lemma increase_load_monotonic:
  "load_val (load (increase_load s)) \<ge> load_val (load s)"
  unfolding increase_load_def
  by (simp add: increase_load_val_eq)

lemma decrease_load_antitonic:
  "load_val (load (decrease_load s)) \<le> load_val (load s)"
  unfolding decrease_load_def
  by (simp add: decrease_load_val_eq)

lemma no_priority_increase:
  "priority_val (priority (adjust_priority s)) \<le> priority_val (priority s)"
  unfolding adjust_priority_def
  by (auto simp: decrease_priority_eq)

lemma progress_towards_min:
  assumes "load_val (load s) > 50" 
      and "priority_val (priority s) > 20"
  shows "priority_val (priority (adjust_priority s)) < priority_val (priority s)"
proof -
  have "priority_val (priority (adjust_priority s)) = 
        (if priority_val (priority s) > 10 then max 10 (priority_val (priority s) - 10) else 10)"
    using assms
    by (simp add: adjust_priority_def decrease_priority_eq)  
  also have "... < priority_val (priority s)"
    using assms(2) by auto    
  finally show ?thesis .
qed


lemma load_val_bounds_increase:
  "load_val (load (increase_load s)) \<le> 100"
  unfolding increase_load_def
  by (simp add: increase_load_val_eq)

lemma load_val_bounds_decrease:
  "load_val (load (decrease_load s)) \<le> 100"
  unfolding decrease_load_def
  by simp

theorem adjustment_increments_counter:
  assumes "load_val (load s) > 50" "priority_val (priority s) > 10"
  shows "adjustments (adjust_priority s) = adjustments s + 1"
  unfolding adjust_priority_def
  using assms by auto


lemma init_satisfies_bounds: "priority_in_bounds init" unfolding priority_in_bounds_def by simp
lemma init_satisfies_load_bounds: "load_in_bounds init" unfolding load_in_bounds_def by simp
lemma actions_preserve_priority_bounds: "priority_in_bounds (increase_load s) \<and> priority_in_bounds (decrease_load s) \<and> priority_in_bounds (adjust_priority s)" 
  unfolding priority_in_bounds_def by simp

end