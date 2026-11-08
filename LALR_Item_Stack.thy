theory LALR_Item_Stack
  imports LALR_Items LALR_Stack
begin

definition item_state_migration ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> state \<Rightarrow>
   state \<Rightarrow> bool" where
  "item_state_migration t items s g \<longleftrightarrow>
     (\<exists>bound symbol0.
        s \<in> states t \<and>
        g \<in> states t \<and>
        state_items items g =
          item_canonical_goto t bound (state_items items s) symbol0)"

definition adjacent_item_consistent ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> state \<Rightarrow>
   state \<Rightarrow> bool" where
  "adjacent_item_consistent t items s g \<longleftrightarrow>
     item_state_migration t items s g"

fun stack_item_consistent_aux ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> state list \<Rightarrow> bool" where
  "stack_item_consistent_aux t items [] = True"
| "stack_item_consistent_aux t items [s] = True"
| "stack_item_consistent_aux t items (s # g # stk) =
     (adjacent_item_consistent t items s g \<and>
      stack_item_consistent_aux t items (g # stk))"

definition stack_item_consistent ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> state list \<Rightarrow> bool" where
  "stack_item_consistent t items stk = stack_item_consistent_aux t items stk"

definition reduce_transition_step ::
  "lalr_table \<Rightarrow> config \<Rightarrow> config \<Rightarrow>
   state \<Rightarrow> state \<Rightarrow> bool" where
  "reduce_transition_step t cfg cfg' s g \<longleftrightarrow>
    (\<exists>rid p stk' s'.
        position cfg < length (input_tokens cfg) \<and>
        top_state (state_stack cfg) = Some s \<and>
        actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
        productions t rid = Some p \<and>
        pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
        top_state stk' = Some s' \<and>
        gotos t s' (lhs p) = Some g \<and>
        top_state (state_stack cfg') = Some g \<and>
        one_step t cfg = Next cfg')"

definition reduce_transition ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> config \<Rightarrow>
   config \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "reduce_transition t toks cfg cfg' s g \<longleftrightarrow>
     reachable_cfg t toks cfg \<and>
     reduce_transition_step t cfg cfg' s g"

definition reduce_transition_correct ::
  "lalr_table \<Rightarrow> bool" where
  "reduce_transition_correct t \<longleftrightarrow>
     (\<forall>toks cfg cfg' s g.
        reduce_transition t toks cfg cfg' s g \<longrightarrow>
        s \<in> states t \<and> g \<in> states t \<and>
        (\<exists>tok rid p s'.
          actions t s tok = Some (ActReduce rid) \<and>
          productions t rid = Some p \<and>
          s' \<in> states t \<and>
          gotos t s' (lhs p) = Some g))"

lemma state_items_certificate_shift_migration:
  assumes certificate:
    "state_items_certificate t mapping bound initial_items"
    and source_state: "s \<in> states t"
    and action: "actions t s tok = Some (ActShift st)"
  shows "item_state_migration t mapping s st"
proof -
  have target:
    "state_items mapping st =
      item_canonical_goto t bound (state_items mapping s)
        (Terminal tok)"
    using state_items_certificate_shiftD[OF certificate source_state action]
    by blast
  have target_state: "st \<in> states t"
    using state_items_certificate_shiftD[OF certificate source_state action]
    by blast
  show ?thesis
    unfolding item_state_migration_def
    apply (rule exI[of _ bound], rule exI[of _ "Terminal tok"])
    using source_state target_state target by simp
qed

lemma state_items_certificate_goto_migration:
  assumes certificate:
    "state_items_certificate t mapping bound initial_items"
    and source_state: "s \<in> states t"
    and goto: "gotos t s nt = Some g"
  shows "item_state_migration t mapping s g"
proof -
  have target:
    "state_items mapping g =
      item_canonical_goto t bound (state_items mapping s)
        (Nonterminal nt)"
    using state_items_certificate_gotoD[OF certificate source_state goto]
    by blast
  have target_state: "g \<in> states t"
    using state_items_certificate_gotoD[OF certificate source_state goto]
    by blast
  show ?thesis
    unfolding item_state_migration_def
    apply (rule exI[of _ bound], rule exI[of _ "Nonterminal nt"])
    using source_state target_state target by simp
qed



end
