theory LALR_Stack
  imports LALR_Recognizer
begin

text \<open>
  Generic well-formedness properties for the recognizer state stack.
  The stack records a path through the table: shifts append a target
  state, while reductions pop a production right-hand side and append
  the corresponding GOTO target.
\<close>

inductive stack_well_formed :: "lalr_table \<Rightarrow> state list \<Rightarrow> bool" where
  stack_well_formed_init:
    "stack_well_formed t [start_state t]"
| stack_well_formed_shift:
    "stack_well_formed t stk
     \<Longrightarrow> top_state stk = Some s
     \<Longrightarrow> actions t s tok = Some (ActShift st)
     \<Longrightarrow> stack_well_formed t (stk @ [st])"
| stack_well_formed_reduce:
    "stack_well_formed t stk
     \<Longrightarrow> productions t rid = Some p
     \<Longrightarrow> pop_rhs (length (rhs p)) stk = Some stk'
     \<Longrightarrow> top_state stk' = Some s'
     \<Longrightarrow> gotos t s' (lhs p) = Some g
     \<Longrightarrow> stack_well_formed t (stk' @ [g])"

definition reachable_stack ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> state list \<Rightarrow> bool" where
  "reachable_stack t toks stk \<longleftrightarrow>
    (\<exists>cfg. reachable_cfg t toks cfg \<and> state_stack cfg = stk)"

lemma stack_well_formed_nonempty:
  "stack_well_formed t stk \<Longrightarrow> stk \<noteq> []"
proof (induction rule: stack_well_formed.induct)
  case stack_well_formed_init
  then show ?case by simp
next
  case stack_well_formed_shift
  then show ?case by simp
next
  case stack_well_formed_reduce
  then show ?case by simp
qed

lemma reachable_stack_well_formed:
  "reachable_cfg t toks cfg
   \<Longrightarrow> stack_well_formed t (state_stack cfg)"
proof (induction rule: reachable_cfg.induct)
  case reachable_cfg_init
  then show ?case
    by (simp add: init_config_def
        stack_well_formed.stack_well_formed_init)
next
  case reachable_cfg_next
  then show ?case
    unfolding one_step_def
    by (auto simp: Let_def append_trace_def config.equality
        split: if_splits option.splits action.splits
        intro: stack_well_formed.intros)
qed

lemma reachable_stack_well_formed_iff:
  "reachable_stack t toks stk
   \<Longrightarrow> stack_well_formed t stk"
  unfolding reachable_stack_def
  by (auto intro: reachable_stack_well_formed)

end
