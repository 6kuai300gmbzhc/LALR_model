theory LALR_Items
  imports LALR_CFG_Bridge
begin

text \<open>
  Basic LR items for the termination generalization.
  An item is identified by a production id and a dot position in its RHS.
  The table remains the source of productions; no table-state/item-set
  correspondence is assumed at this layer.
\<close>

type_synonym lr_item = "production_id \<times> nat"
type_synonym item_set = "lr_item set"
type_synonym state_item_map = "state \<Rightarrow> item_set"
type_synonym item_lookahead_map = "lr_item \<Rightarrow> token set"
type_synonym state_lookahead_map = "state \<Rightarrow> item_lookahead_map"

definition state_items ::
  "state_item_map \<Rightarrow> state \<Rightarrow> item_set" where
  "state_items mapping s = mapping s"

definition state_item_lookaheads ::
  "state_lookahead_map \<Rightarrow> state \<Rightarrow>
   lr_item \<Rightarrow> token set" where
  "state_item_lookaheads mapping s item = mapping s item"

definition lookahead_item_set ::
  "state_item_map \<Rightarrow> state_lookahead_map \<Rightarrow> state \<Rightarrow>
   (lr_item \<times> token set) set" where
  "lookahead_item_set items lookaheads s =
      {pair. \<exists>item \<in> state_items items s.
        pair = (item, state_item_lookaheads lookaheads s item)}"

definition item_well_formed ::
  "lalr_table \<Rightarrow> lr_item \<Rightarrow> bool" where
  "item_well_formed t item \<longleftrightarrow>
     (\<exists>p. productions t (fst item) = Some p \<and>
       snd item \<le> length (rhs p))"

definition item_set_well_formed ::
  "lalr_table \<Rightarrow> item_set \<Rightarrow> bool" where
  "item_set_well_formed t items \<longleftrightarrow>
     (\<forall>item \<in> items. item_well_formed t item)"

definition item_complete ::
  "lalr_table \<Rightarrow> lr_item \<Rightarrow> bool" where
  "item_complete t item \<longleftrightarrow>
     (\<exists>p. productions t (fst item) = Some p \<and>
       snd item = length (rhs p))"

definition item_symbol_after ::
  "lalr_table \<Rightarrow> lr_item \<Rightarrow>
   symbol grammar_symbol option" where
  "item_symbol_after t item =
     (case productions t (fst item) of
        None \<Rightarrow> None
      | Some p \<Rightarrow>
          if snd item < length (rhs p)
          then Some ((rhs p) ! (snd item))
          else None)"

definition item_advance ::
  "lr_item \<Rightarrow> lr_item" where
  "item_advance item = (fst item, Suc (snd item))"

definition item_shiftable ::
  "lalr_table \<Rightarrow> lr_item \<Rightarrow> bool" where
  "item_shiftable t item \<longleftrightarrow>
     item_symbol_after t item \<noteq> None"

definition item_goto ::
  "lalr_table \<Rightarrow> item_set \<Rightarrow>
  symbol grammar_symbol \<Rightarrow> item_set" where
  "item_goto t items symbol0 =
     {item0. \<exists>item. item \<in> items \<and>
       item_symbol_after t item = Some symbol0 \<and>
       item0 = item_advance item}"

definition item_closure_step ::
  "lalr_table \<Rightarrow> item_set \<Rightarrow> item_set" where
  "item_closure_step t items =
     items \<union>
      {item0. \<exists>rid item nt p.
        item0 = (rid, 0) \<and>
        item \<in> items \<and>
        item_symbol_after t item = Some (Nonterminal nt) \<and>
        productions t rid = Some p \<and>
        lhs p = nt}"

fun item_closure_iter ::
  "lalr_table \<Rightarrow> nat \<Rightarrow> item_set \<Rightarrow> item_set" where
  "item_closure_iter t 0 items = items"
| "item_closure_iter t (Suc n) items =
     item_closure_iter t n (item_closure_step t items)"

definition item_closure ::
  "lalr_table \<Rightarrow> nat \<Rightarrow> item_set \<Rightarrow> item_set" where
  "item_closure t bound items = item_closure_iter t bound items"

definition item_canonical_goto ::
  "lalr_table \<Rightarrow> nat \<Rightarrow> item_set \<Rightarrow>
   symbol grammar_symbol \<Rightarrow> item_set" where
  "item_canonical_goto t bound items symbol0 =
     item_closure t bound (item_goto t items symbol0)"

definition lalr_lookahead_certificate ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   state_lookahead_map \<Rightarrow> bool" where
  "lalr_lookahead_certificate t items lookaheads \<longleftrightarrow>
     (\<forall>s \<in> states t. \<forall>item \<in> state_items items s.
        state_item_lookaheads lookaheads s item \<subseteq> terminals t)"

definition state_items_certificate ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> nat \<Rightarrow>
   item_set \<Rightarrow> bool" where
  "state_items_certificate t mapping bound initial_items \<longleftrightarrow>
     (\<forall>s \<in> states t.
        item_set_well_formed t (state_items mapping s))
     \<and> state_items mapping (start_state t) =
       item_closure t bound initial_items
     \<and> (\<forall>s tok st.
        s \<in> states t \<longrightarrow>
        actions t s tok = Some (ActShift st) \<longrightarrow>
        st \<in> states t \<and>
        state_items mapping st =
          item_canonical_goto t bound (state_items mapping s)
            (Terminal tok))
     \<and> (\<forall>s nt g.
        s \<in> states t \<longrightarrow>
        gotos t s nt = Some g \<longrightarrow>
        g \<in> states t \<and>
        state_items mapping g =
          item_canonical_goto t bound (state_items mapping s)
            (Nonterminal nt))
     \<and> (\<forall>s tok rid.
        s \<in> states t \<longrightarrow>
        actions t s tok = Some (ActReduce rid) \<longrightarrow>
        (\<exists>p. productions t rid = Some p \<and>
          (rid, length (rhs p)) \<in> state_items mapping s))"

definition lalr_shift_action_correct ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow> bool" where
  "lalr_shift_action_correct t items \<longleftrightarrow>
     (\<forall>s tok st item.
        s \<in> states t \<longrightarrow>
        actions t s tok = Some (ActShift st) \<longrightarrow>
        item \<in> state_items items s \<longrightarrow>
        item_symbol_after t item = Some (Terminal tok) \<longrightarrow>
        item_advance item \<in> state_items items st)"

definition lalr_reduce_action_correct ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   state_lookahead_map \<Rightarrow> bool" where
  "lalr_reduce_action_correct t items lookaheads \<longleftrightarrow>
     (\<forall>s tok rid.
        s \<in> states t \<longrightarrow>
        actions t s tok = Some (ActReduce rid) \<longrightarrow>
        (\<exists>p.
          productions t rid = Some p \<and>
          item_complete t (rid, length (rhs p)) \<and>
          (rid, length (rhs p)) \<in> state_items items s \<and>
          tok \<in> state_item_lookaheads lookaheads s
            (rid, length (rhs p))))"

definition lalr_accept_action_correct ::
  "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   state_lookahead_map \<Rightarrow> bool" where
  "lalr_accept_action_correct G t items lookaheads \<longleftrightarrow>
     (\<forall>s.
        s \<in> states t \<longrightarrow>
        actions t s end_token = Some ActAccept \<longrightarrow>
        (\<exists>rid p.
          productions t rid = Some p \<and>
          rhs p = [Nonterminal (\<SS> G)] \<and>
          item_complete t (rid, length (rhs p)) \<and>
          (rid, length (rhs p)) \<in> state_items items s \<and>
          end_token \<in> state_item_lookaheads lookaheads s
            (rid, length (rhs p))))"

definition lalr_table_generation_certificate ::
  "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   state_lookahead_map \<Rightarrow> nat \<Rightarrow> item_set \<Rightarrow> bool" where
  "lalr_table_generation_certificate G t items lookaheads bound initial_items
     \<longleftrightarrow>
     state_items_certificate t items bound initial_items \<and>
     lalr_lookahead_certificate t items lookaheads \<and>
     lalr_shift_action_correct t items \<and>
     lalr_reduce_action_correct t items lookaheads \<and>
     lalr_accept_action_correct G t items lookaheads"

lemma lalr_table_generation_certificateD:
  "lalr_table_generation_certificate G t items lookaheads bound initial_items
   \<Longrightarrow>
   state_items_certificate t items bound initial_items \<and>
   lalr_lookahead_certificate t items lookaheads \<and>
   lalr_shift_action_correct t items \<and>
   lalr_reduce_action_correct t items lookaheads \<and>
   lalr_accept_action_correct G t items lookaheads"
  by (simp add: lalr_table_generation_certificate_def)

lemma item_complete_well_formed:
  "item_complete t item \<Longrightarrow> item_well_formed t item"
proof -
  assume complete: "item_complete t item"
  obtain p where
    production: "productions t (fst item) = Some p"
    and position: "snd item = length (rhs p)"
    using complete unfolding item_complete_def by blast
  show "item_well_formed t item"
    unfolding item_well_formed_def
    using production position by simp
qed

lemma item_advance_fst:
  "fst (item_advance item) = fst item"
  by (simp add: item_advance_def)

lemma item_advance_snd:
  "snd (item_advance item) = Suc (snd item)"
  by (simp add: item_advance_def)

lemma item_shiftable_iff_symbol_after:
  "item_shiftable t item \<longleftrightarrow>
   item_symbol_after t item \<noteq> None"
  unfolding item_shiftable_def by simp

lemma item_set_well_formed_member:
  assumes "item_set_well_formed t items"
    and "item \<in> items"
  shows "item_well_formed t item"
  using assms unfolding item_set_well_formed_def by blast

lemma item_goto_member:
  assumes "item \<in> item_goto t items (symbol0 :: symbol grammar_symbol)"
  shows "\<exists>item0. item0 \<in> items \<and>
    item_symbol_after t item0 = Some symbol0 \<and>
    item = item_advance item0"
  using assms unfolding item_goto_def by blast

lemma item_closure_step_member:
  "item \<in> item_closure_step t items \<longleftrightarrow>
   item \<in> items \<or>
  (\<exists>rid item0 nt p.
    item = (rid, 0) \<and>
      item0 \<in> items \<and>
      item_symbol_after t item0 = Some (Nonterminal nt) \<and>
    productions t rid = Some p \<and>
    lhs p = nt)"
  unfolding item_closure_step_def by simp

lemma item_set_well_formed_closure_step:
  assumes "item_set_well_formed t items"
  shows "item_set_well_formed t (item_closure_step t items)"
  unfolding item_set_well_formed_def item_closure_step_def
  using assms unfolding item_set_well_formed_def item_well_formed_def
  by auto

lemma item_closure_iter_zero:
  "item_closure_iter t 0 items = items"
  by simp

lemma item_closure_iter_Suc:
  "item_closure_iter t (Suc n) items =
   item_closure_iter t n (item_closure_step t items)"
  by simp

lemma item_closure_subset:
  "items \<subseteq> item_closure t bound items"
proof (induction bound arbitrary: items)
  case 0
  then show ?case
    unfolding item_closure_def
    by simp
next
  case (Suc bound)
  have step_subset:
    "items \<subseteq> item_closure_step t items"
    unfolding item_closure_step_def by simp
  have iter_subset:
    "item_closure_step t items \<subseteq>
       item_closure t bound (item_closure_step t items)"
    using Suc.IH[of "item_closure_step t items"]
    unfolding item_closure_def by simp
  have closure_eq:
    "item_closure t (Suc bound) items =
       item_closure t bound (item_closure_step t items)"
    unfolding item_closure_def by simp
  show ?case
    unfolding closure_eq
    using subset_trans[OF step_subset iter_subset] .
qed

lemma item_set_well_formed_closure_aux:
  "item_set_well_formed t items \<Longrightarrow>
   item_set_well_formed t (item_closure t bound items)"
proof (induction bound arbitrary: items)
  case 0
  then show ?case
    by (simp add: item_closure_def)
next
  case (Suc bound)
  have step_wf:
    "item_set_well_formed t (item_closure_step t items)"
    by (rule item_set_well_formed_closure_step[OF Suc.prems])
  have smaller:
    "item_set_well_formed t
      (item_closure t bound (item_closure_step t items))"
    using Suc.IH[of "item_closure_step t items"] step_wf by blast
  show ?case
    using smaller unfolding item_closure_def by simp
qed

lemma item_set_well_formed_closure:
  assumes "item_set_well_formed t items"
  shows "item_set_well_formed t (item_closure t bound items)"
  using item_set_well_formed_closure_aux[OF assms, of bound] .

lemma item_canonical_goto_member:
  assumes "item \<in> item_canonical_goto t bound items
    (symbol0 :: symbol grammar_symbol)"
  shows "item \<in> item_closure t bound (item_goto t items symbol0)"
  using assms unfolding item_canonical_goto_def by simp

lemma state_items_certificateD:
  assumes "state_items_certificate t mapping bound initial_items"
    and "s \<in> states t"
  shows "item_set_well_formed t (state_items mapping s)"
  using assms unfolding state_items_certificate_def by blast

lemma state_items_certificate_shiftD:
  assumes "state_items_certificate t mapping bound initial_items"
    and "s \<in> states t"
    and "actions t s tok = Some (ActShift st)"
  shows "st \<in> states t \<and>
    state_items mapping st =
      item_canonical_goto t bound (state_items mapping s)
        (Terminal tok)"
  using assms unfolding state_items_certificate_def by blast

lemma state_items_certificate_gotoD:
  assumes "state_items_certificate t mapping bound initial_items"
    and "s \<in> states t"
    and "gotos t s nt = Some g"
  shows "g \<in> states t \<and>
    state_items mapping g =
      item_canonical_goto t bound (state_items mapping s)
        (Nonterminal nt)"
  using assms unfolding state_items_certificate_def by blast

lemma state_items_shift_migration:
  assumes certificate:
    "state_items_certificate t mapping bound initial_items"
    and source_state: "s \<in> states t"
    and action: "actions t s tok = Some (ActShift st)"
    and source_item: "item \<in> state_items mapping s"
    and after: "item_symbol_after t item = Some (Terminal tok)"
  shows "item_advance item \<in> state_items mapping st"
proof -
  have target:
    "state_items mapping st =
      item_canonical_goto t bound (state_items mapping s)
        (Terminal tok)"
    using state_items_certificate_shiftD[OF certificate source_state action]
    by simp
  have moved:
    "item_advance item \<in>
      item_goto t (state_items mapping s) (Terminal tok)"
    unfolding item_goto_def
    using source_item after by blast
  have in_closure:
    "item_advance item \<in>
      item_closure t bound
        (item_goto t (state_items mapping s) (Terminal tok))"
    using item_closure_subset
      [where t = t and bound = bound
        and items = "item_goto t (state_items mapping s) (Terminal tok)"] moved
    by blast
  show ?thesis
    using target in_closure
    unfolding item_canonical_goto_def by simp
qed

lemma state_items_goto_migration:
  assumes certificate:
    "state_items_certificate t mapping bound initial_items"
    and source_state: "s \<in> states t"
    and goto: "gotos t s nt = Some g"
    and source_item: "item \<in> state_items mapping s"
    and after: "item_symbol_after t item = Some (Nonterminal nt)"
  shows "item_advance item \<in> state_items mapping g"
proof -
  have target:
    "state_items mapping g =
      item_canonical_goto t bound (state_items mapping s)
        (Nonterminal nt)"
    using state_items_certificate_gotoD[OF certificate source_state goto]
    by simp
  have moved:
    "item_advance item \<in>
      item_goto t (state_items mapping s) (Nonterminal nt)"
    unfolding item_goto_def
    using source_item after by blast
  have in_closure:
    "item_advance item \<in>
      item_closure t bound
        (item_goto t (state_items mapping s) (Nonterminal nt))"
    using item_closure_subset
      [where t = t and bound = bound
        and items = "item_goto t (state_items mapping s) (Nonterminal nt)"] moved
    by blast
  show ?thesis
    using target in_closure
    unfolding item_canonical_goto_def by simp
qed

lemma state_items_certificate_reduceD:
  assumes "state_items_certificate t mapping bound initial_items"
    and "s \<in> states t"
    and "actions t s tok = Some (ActReduce rid)"
  shows "\<exists>p. productions t rid = Some p \<and>
    (rid, length (rhs p)) \<in> state_items mapping s"
  using assms unfolding state_items_certificate_def by blast

lemma state_items_reduce_migration:
  assumes certificate:
    "state_items_certificate t mapping bound initial_items"
    and source_state: "s \<in> states t"
    and action: "actions t s tok = Some (ActReduce rid)"
  shows "\<exists>p. productions t rid = Some p \<and>
    item_complete t (rid, length (rhs p)) \<and>
    (rid, length (rhs p)) \<in> state_items mapping s"
proof -
  obtain p where production: "productions t rid = Some p"
    and member: "(rid, length (rhs p)) \<in> state_items mapping s"
    using state_items_certificate_reduceD[OF certificate source_state action]
    by blast
  show ?thesis
  proof (rule exI[where x = p], intro conjI)
    show "productions t rid = Some p"
      by (rule production)
  next
    show "item_complete t (rid, length (rhs p))"
      unfolding item_complete_def
      using production by simp
  next
    show "(rid, length (rhs p)) \<in> state_items mapping s"
      by (rule member)
  qed
qed

end
