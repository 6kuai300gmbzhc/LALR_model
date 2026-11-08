theory LALR_Termination
  imports LALR_Invariant LALR_Item_Stack
begin

text \<open>
  Termination interface for the table-driven recognizer.
  The executable recognizer remains fuel-based; this theory states the
  semantic assumptions needed to remove the fuel bound.
\<close>

definition shift_step ::
  "lalr_table \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "shift_step t cfg cfg' \<longleftrightarrow>
     (\<exists>s st.
      top_state (state_stack cfg) = Some s \<and>
      position cfg < length (input_tokens cfg) \<and>
      actions t s (input_tokens cfg ! position cfg) = Some (ActShift st) \<and>
       one_step t cfg = Next cfg')"


  lemma pop_rhs_subset:
    "pop_rhs n stk = Some stk' \<Longrightarrow> set stk' \<subseteq> set stk"
    unfolding pop_rhs_def by (auto intro: in_set_takeD split: if_splits)

  lemma pop_rhs_member:
    "pop_rhs n stk = Some stk' \<Longrightarrow> x \<in> set stk' \<Longrightarrow> x \<in> set stk"
    unfolding pop_rhs_def by (auto intro: in_set_takeD split: if_splits)

  lemma top_state_member:
    "top_state stk = Some s \<Longrightarrow> s \<in> set stk"
    unfolding top_state_def by (auto split: if_splits)

  lemma stack_well_formed_states:
    "stack_well_formed t stk \<Longrightarrow> wf_table t \<Longrightarrow> set stk \<subseteq> states t"
  proof (induction rule: stack_well_formed.induct)
    case stack_well_formed_init
    then show ?case by (simp add: wf_table_def)
  next
    case stack_well_formed_shift
    then show ?case by (auto simp: wf_table_def)
  next
    case stack_well_formed_reduce
    then show ?case using pop_rhs_member by (auto simp: wf_table_def)
  qed

  lemma reachable_cfg_stack_states:
    "wf_table t \<Longrightarrow> reachable_cfg t toks cfg \<Longrightarrow>
       set (state_stack cfg) \<subseteq> states t"
    by (rule stack_well_formed_states[OF reachable_stack_well_formed])

  lemma reduce_transition_step_obtain:
    assumes "reduce_transition_step t cfg cfg' s g"
    shows "\<exists>rid p stk' s'.
       position cfg < length (input_tokens cfg) \<and>
       top_state (state_stack cfg) = Some s \<and>
       actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
       productions t rid = Some p \<and>
       pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
       top_state stk' = Some s' \<and>
       gotos t s' (lhs p) = Some g \<and>
       top_state (state_stack cfg') = Some g \<and>
       one_step t cfg = Next cfg'"
    using assms unfolding reduce_transition_step_def by blast

  lemma wf_table_reduce_transition_correct:
    "wf_table t \<Longrightarrow> reduce_transition_correct t"
    unfolding reduce_transition_correct_def
  proof (intro impI allI impI)
    fix toks cfg cfg' s g
    assume wf_t: "wf_table t"
    assume rt: "reduce_transition t toks cfg cfg' s g"
    have reach: "reachable_cfg t toks cfg"
      using rt unfolding reduce_transition_def by blast
    have step: "reduce_transition_step t cfg cfg' s g"
      using rt unfolding reduce_transition_def by blast
    have stack_states: "set (state_stack cfg) \<subseteq> states t"
      by (rule reachable_cfg_stack_states[OF wf_t reach])
    have top: "top_state (state_stack cfg) = Some s"
      using step unfolding reduce_transition_step_def by blast
    have s_states: "s \<in> states t"
      using top stack_states top_state_member by blast
    from reduce_transition_step_obtain[OF step] obtain rid p stk' s' where dec:
      "position cfg < length (input_tokens cfg) \<and>
       top_state (state_stack cfg) = Some s \<and>
       actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
       productions t rid = Some p \<and>
       pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
       top_state stk' = Some s' \<and>
       gotos t s' (lhs p) = Some g \<and>
       top_state (state_stack cfg') = Some g \<and>
       one_step t cfg = Next cfg'"
      by blast
    have g_states: "g \<in> states t"
        using wf_t dec unfolding wf_table_def by blast
    have act: "actions t s (input_tokens cfg ! position cfg) =
        Some (ActReduce rid)"
      using dec by blast
    have prod: "productions t rid = Some p"
      using dec by blast
    have pop: "pop_rhs (length (rhs p)) (state_stack cfg) = Some stk'"
      using dec by blast
    have goto: "gotos t s' (lhs p) = Some g"
      using dec by blast
    have subset: "set stk' \<subseteq> set (state_stack cfg)"
      by (rule pop_rhs_subset[OF pop])
    have s'_states: "s' \<in> states t"
        using dec subset stack_states top_state_member by blast
    show "s \<in> states t \<and> g \<in> states t \<and>
      (\<exists>tok rid p s'.
        actions t s tok = Some (ActReduce rid) \<and>
        productions t rid = Some p \<and>
        s' \<in> states t \<and>
        gotos t s' (lhs p) = Some g)"
    proof (intro conjI)
      show "s \<in> states t" using s_states .
    next
      show "g \<in> states t" using g_states .
    next
      show "\<exists>tok rid p s'.
        actions t s tok = Some (ActReduce rid) \<and>
        productions t rid = Some p \<and>
        s' \<in> states t \<and>
        gotos t s' (lhs p) = Some g"
        by (rule_tac x="input_tokens cfg ! position cfg" in exI,
            rule_tac x=rid in exI, rule_tac x=p in exI, rule_tac x=s' in exI,
          intro conjI, rule act, rule prod, rule s'_states, rule goto)
    qed
  qed
definition reduce_step ::
  "lalr_table \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "reduce_step t cfg cfg' \<longleftrightarrow>
    (\<exists>s rid.
      position cfg < length (input_tokens cfg) \<and>
      top_state (state_stack cfg) = Some s \<and>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
      one_step t cfg = Next cfg')"

definition reduce_state_edge ::
  "lalr_table \<Rightarrow> config \<Rightarrow> config \<Rightarrow>
   state \<Rightarrow> state \<Rightarrow> bool" where
  "reduce_state_edge t cfg cfg' s g \<longleftrightarrow>
     reduce_step t cfg cfg' \<and>
     top_state (state_stack cfg) = Some s \<and>
     top_state (state_stack cfg') = Some g"

definition reduce_graph ::
  "lalr_table \<Rightarrow> (state \<times> state) set" where
  "reduce_graph t =
     {(s,g). s \<in> states t \<and>
       (\<exists>tok rid p s'.
          actions t s tok = Some (ActReduce rid) \<and>
          productions t rid = Some p \<and>
          s' \<in> states t \<and>
          gotos t s' (lhs p) = Some g) \<and>
       g \<in> states t}"

definition finite_reduce_graph :: "lalr_table \<Rightarrow> bool" where
  "finite_reduce_graph t \<longleftrightarrow> finite (states t)"

definition reduce_state_rank_certificate ::
  "lalr_table \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> bool" where
  "reduce_state_rank_certificate t state_rank \<longleftrightarrow>
     (\<forall>s g. (s,g) \<in> reduce_graph t \<longrightarrow>
       state_rank g < state_rank s)"

definition reduce_rank_of_state ::
  "(state \<Rightarrow> nat) \<Rightarrow> config \<Rightarrow> nat" where
  "reduce_rank_of_state state_rank cfg =
     (case top_state (state_stack cfg) of
        None \<Rightarrow> 0
      | Some s \<Rightarrow> state_rank s)"

definition reduce_graph_edge_certificate ::
  "(config \<Rightarrow> bool) \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "reduce_graph_edge_certificate reachable t \<longleftrightarrow>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       reduce_step t cfg cfg' \<longrightarrow>
       (\<exists>s g. reduce_state_edge t cfg cfg' s g \<and>
         (s,g) \<in> reduce_graph t))"

lemma reduce_graph_subset_states:
  "reduce_graph t \<subseteq> states t \<times> states t"
  unfolding reduce_graph_def
  by auto

lemma finite_reduce_graphI:
  assumes "finite (states t)"
  shows "finite (reduce_graph t)"
proof -
  have finite_states_product: "finite (states t \<times> states t)"
    using assms by simp
  show ?thesis
    by (rule finite_subset[OF reduce_graph_subset_states finite_states_product])
qed

lemma finite_reduce_graphD:
  assumes "finite_reduce_graph t"
  shows "finite (reduce_graph t)"
  using assms unfolding finite_reduce_graph_def by (rule finite_reduce_graphI)

lemma reduce_graph_edge_certificateD:
  assumes "reduce_graph_edge_certificate reachable t"
    and "reachable cfg"
    and "reduce_step t cfg cfg'"
  shows "\<exists>s g. reduce_state_edge t cfg cfg' s g \<and>
    (s,g) \<in> reduce_graph t"
  using assms unfolding reduce_graph_edge_certificate_def by blast

lemma reduce_graph_rank_decreases:
  assumes graph_rank:
    "reduce_state_rank_certificate t state_rank"
    and edge: "(s,g) \<in> reduce_graph t"
  shows "state_rank g < state_rank s"
  using graph_rank edge unfolding reduce_state_rank_certificate_def by blast

lemma reduce_rank_of_state_decreases:
  assumes graph_rank:
    "reduce_state_rank_certificate t state_rank"
    and before: "top_state (state_stack cfg) = Some s"
    and after: "top_state (state_stack cfg') = Some g"
    and edge: "(s,g) \<in> reduce_graph t"
  shows "reduce_rank_of_state state_rank cfg' <
    reduce_rank_of_state state_rank cfg"
  using reduce_graph_rank_decreases[OF graph_rank edge] before after
  unfolding reduce_rank_of_state_def by simp

lemma reachable_reduce_rank_decreases:
  assumes edge_certificate:
    "reduce_graph_edge_certificate reachable t"
    and graph_rank:
    "reduce_state_rank_certificate t state_rank"
    and reachable: "reachable cfg"
    and reduce: "reduce_step t cfg cfg'"
  shows "reduce_rank_of_state state_rank cfg' <
    reduce_rank_of_state state_rank cfg"
proof -
  obtain s g where
    state_edge: "reduce_state_edge t cfg cfg' s g"
    and graph_edge: "(s,g) \<in> reduce_graph t"
    using reduce_graph_edge_certificateD
      [OF edge_certificate reachable reduce] by blast
  obtain before: "top_state (state_stack cfg) = Some s"
    and after: "top_state (state_stack cfg') = Some g"
    using state_edge unfolding reduce_state_edge_def by blast
  show "reduce_rank_of_state state_rank cfg' <
    reduce_rank_of_state state_rank cfg"
    by (rule reduce_rank_of_state_decreases
        [OF graph_rank before after graph_edge])
qed

definition reduce_rank_certificate ::
  "(config \<Rightarrow> bool) \<Rightarrow>
   (config \<Rightarrow> nat) \<Rightarrow>
   lalr_table \<Rightarrow> bool" where
  "reduce_rank_certificate reachable rank t \<longleftrightarrow>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       reduce_step t cfg cfg' \<longrightarrow> rank cfg' < rank cfg)"

definition reduce_edge_certificate ::
  "(config \<Rightarrow> bool) \<Rightarrow>
   (state \<times> state) set \<Rightarrow>
   lalr_table \<Rightarrow> bool" where
  "reduce_edge_certificate reachable edges t \<longleftrightarrow>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       reduce_step t cfg cfg' \<longrightarrow>
       (\<exists>s g. reduce_state_edge t cfg cfg' s g \<and>
         (s,g) \<in> edges))"

lemma reduce_edge_certificateD:
  assumes "reduce_edge_certificate reachable edges t"
    and "reachable cfg"
    and "reduce_step t cfg cfg'"
  shows "\<exists>s g. reduce_state_edge t cfg cfg' s g \<and> (s,g) \<in> edges"
  using assms unfolding reduce_edge_certificate_def by blast

lemma reduce_rank_certificateD:
  assumes "reduce_rank_certificate reachable rank t"
    and "reachable cfg"
    and "reduce_step t cfg cfg'"
  shows "rank cfg' < rank cfg"
  using assms unfolding reduce_rank_certificate_def by blast

lemma reduce_graph_rank_certificate:
  assumes edge_certificate:
    "reduce_graph_edge_certificate reachable t"
    and graph_rank:
    "reduce_state_rank_certificate t state_rank"
  shows "reduce_rank_certificate reachable
    (reduce_rank_of_state state_rank) t"
  unfolding reduce_rank_certificate_def
proof (intro allI allI impI impI)
  fix cfg cfg'
  assume reachable: "reachable cfg"
  assume reduce: "reduce_step t cfg cfg'"
  show "reduce_rank_of_state state_rank cfg' <
    reduce_rank_of_state state_rank cfg"
    by (rule reachable_reduce_rank_decreases
        [OF edge_certificate graph_rank reachable reduce])
qed

lemma reduce_step_has_state_edge:
  "reduce_step t cfg cfg' \<Longrightarrow>
   \<exists>s g. reduce_state_edge t cfg cfg' s g"
  unfolding reduce_state_edge_def reduce_step_def
  by (auto simp: one_step_def append_trace_def top_state_def
      split: if_splits option.splits action.splits)

lemma next_is_shift_or_reduce:
  assumes "one_step t cfg = Next cfg'"
  shows "shift_step t cfg cfg' \<or> reduce_step t cfg cfg'"
  using assms
  unfolding shift_step_def reduce_step_def
  by (case_tac "position cfg < length (input_tokens cfg)";
      case_tac "state_stack cfg = []";
      case_tac "actions t (last (state_stack cfg))
        (input_tokens cfg ! position cfg)";
      case_tac "a :: action";
      simp_all add: one_step_def top_state_def append_trace_def
        split: option.splits action.splits)

lemma reduce_step_obtain:
  assumes "reduce_step t cfg cfg'"
  shows "\<exists>s rid.
     position cfg < length (input_tokens cfg) \<and>
     top_state (state_stack cfg) = Some s \<and>
     actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
     one_step t cfg = Next cfg'"
  using assms unfolding reduce_step_def by blast

lemma reduce_graph_edge_certificate_of_transition_correct:
  assumes correct: "reduce_transition_correct t"
    and source: "\<And>cfg. reachable cfg \<Longrightarrow>
      \<exists>toks. reachable_cfg t toks cfg"
  shows "reduce_graph_edge_certificate reachable t"
  unfolding reduce_graph_edge_certificate_def
proof (intro allI impI)
  fix cfg cfg'
  assume reach: "reachable cfg" and red: "reduce_step t cfg cfg'"
  obtain toks where rcfg: "reachable_cfg t toks cfg"
    using source[OF reach] by blast
  from reduce_step_obtain[OF red] obtain s rid where reddec:
    "position cfg < length (input_tokens cfg) \<and>
     top_state (state_stack cfg) = Some s \<and>
     actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
     one_step t cfg = Next cfg'"
    by blast
  have pos: "position cfg < length (input_tokens cfg)"
    using reddec by blast
  have top: "top_state (state_stack cfg) = Some s"
    using reddec by blast
  have act: "actions t s (input_tokens cfg ! position cfg) =
      Some (ActReduce rid)"
    using reddec by blast
  have nxt: "one_step t cfg = Next cfg'"
    using reddec by blast
  have dec: "\<exists>p stk' s' g.
      productions t rid = Some p \<and>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
      top_state stk' = Some s' \<and>
      gotos t s' (lhs p) = Some g \<and>
      state_stack cfg' = stk' @ [g]"
    using pos top act nxt
    unfolding one_step_def Let_def
    by (auto simp: append_trace_def
        split: option.splits action.splits if_splits)
  then obtain p stk' s' g where dec2:
    "productions t rid = Some p \<and>
     pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
     top_state stk' = Some s' \<and>
     gotos t s' (lhs p) = Some g \<and>
     state_stack cfg' = stk' @ [g]"
    by blast
  have prod: "productions t rid = Some p" using dec2 by blast
  have pop: "pop_rhs (length (rhs p)) (state_stack cfg) = Some stk'"
    using dec2 by blast
  have tops': "top_state stk' = Some s'" using dec2 by blast
  have goto: "gotos t s' (lhs p) = Some g" using dec2 by blast
  have stack': "state_stack cfg' = stk' @ [g]" using dec2 by blast
  have topg: "top_state (state_stack cfg') = Some g"
    using stack' by (simp add: top_state_def)
  have rt_step: "reduce_transition_step t cfg cfg' s g"
    unfolding reduce_transition_step_def
    using pos top act prod pop tops' goto topg nxt by blast
  have rt: "reduce_transition t toks cfg cfg' s g"
    unfolding reduce_transition_def using rcfg rt_step by blast
  have corr: "s \<in> states t \<and> g \<in> states t \<and>
      (\<exists>tok rid p s'. actions t s tok = Some (ActReduce rid) \<and>
        productions t rid = Some p \<and> s' \<in> states t \<and>
        gotos t s' (lhs p) = Some g)"
    using correct[unfolded reduce_transition_correct_def, rule_format, OF rt] .
  have edge: "reduce_state_edge t cfg cfg' s g"
    unfolding reduce_state_edge_def using red top topg by blast
  have mem: "(s,g) \<in> reduce_graph t"
    unfolding reduce_graph_def using corr by blast
  show "\<exists>s g. reduce_state_edge t cfg cfg' s g \<and> (s,g) \<in> reduce_graph t"
    by (rule_tac x=s in exI, rule_tac x=g in exI, intro conjI, rule edge, rule mem)
qed

definition reduce_rel ::
  "lalr_table \<Rightarrow> (config \<times> config) set" where
  "reduce_rel t = {(cfg, cfg'). reduce_step t cfg cfg'}"

definition shift_consumes_token ::
  "lalr_table \<Rightarrow> bool" where
  "shift_consumes_token t \<longleftrightarrow>
     (\<forall>cfg cfg'. shift_step t cfg cfg' \<longrightarrow>
       position cfg' = Suc (position cfg))"

definition stack_operations_well_defined ::
  "lalr_table \<Rightarrow> bool" where
  "stack_operations_well_defined t \<longleftrightarrow>
     (\<forall>cfg cfg'. one_step t cfg = Next cfg' \<longrightarrow>
       state_stack cfg' \<noteq> [])"

definition accept_error_terminal :: "lalr_table \<Rightarrow> bool" where
  "accept_error_terminal t \<longleftrightarrow>
    (\<forall>cfg r cfg'. one_step t cfg = Done r \<longrightarrow>
       one_step t cfg \<noteq> Next cfg')"

definition stage_measure ::
  "token list \<Rightarrow> (config \<Rightarrow> nat) \<Rightarrow> config \<Rightarrow> nat \<times> nat" where
  "stage_measure toks rank cfg =
  (length (toks @ [end_token]) - position cfg, rank cfg)"

definition stage_rel ::
  "token list \<Rightarrow> (config \<Rightarrow> nat) \<Rightarrow> (config \<times> config) set" where
  "stage_rel toks rank = measures
     [\<lambda>cfg. fst (stage_measure toks rank cfg),
      \<lambda>cfg. snd (stage_measure toks rank cfg)]"

definition term_cond ::
  "lalr_table \<Rightarrow> token list \<Rightarrow>
   (config \<Rightarrow> nat) \<Rightarrow> bool" where
  "term_cond t toks reduce_rank \<longleftrightarrow>
     (\<forall>cfg cfg'.
       input_invariant toks cfg \<longrightarrow>
       one_step t cfg = Next cfg' \<longrightarrow>
       (cfg', cfg) \<in> stage_rel toks reduce_rank)"

definition input_invariant_preserved ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "input_invariant_preserved t toks \<longleftrightarrow>
     (\<forall>cfg cfg'.
       input_invariant toks cfg \<longrightarrow>
       one_step t cfg = Next cfg' \<longrightarrow>
       input_invariant toks cfg')"

lemma shift_stage_decreases:
  assumes "shift_step t cfg cfg'"
    and "input_invariant toks cfg"
    and "position cfg < length (input_tokens cfg)"
  shows "(cfg', cfg) \<in> stage_rel toks rank"
  using assms
  unfolding shift_step_def input_invariant_def stage_rel_def stage_measure_def
  by (auto simp: one_step_def append_trace_def split: option.splits action.splits)

lemma reduce_stage_decreases:
  assumes "reduce_step t cfg cfg'"
    and "input_invariant toks cfg"
    and "rank cfg' < rank cfg"
  shows "(cfg', cfg) \<in> stage_rel toks rank"
  using assms
  unfolding reduce_step_def input_invariant_def stage_rel_def stage_measure_def
  by (auto simp: one_step_def append_trace_def split: option.splits action.splits)

lemma next_stage_decreases:
  assumes invariant: "input_invariant toks cfg"
    and next_step: "one_step t cfg = Next cfg'"
    and shift_bound: "shift_step t cfg cfg' \<longrightarrow>
      position cfg < length (input_tokens cfg)"
    and reduce_rank: "reduce_step t cfg cfg' \<longrightarrow> rank cfg' < rank cfg"
  shows "(cfg', cfg) \<in> stage_rel toks rank"
proof -
  have classified: "shift_step t cfg cfg' \<or> reduce_step t cfg cfg'"
    by (rule next_is_shift_or_reduce[OF next_step])
  have shift_case:
    "shift_step t cfg cfg' \<Longrightarrow> (cfg', cfg) \<in> stage_rel toks rank"
  proof -
    assume shift: "shift_step t cfg cfg'"
    have bound: "position cfg < length (input_tokens cfg)"
      using shift_bound shift by blast
    show "(cfg', cfg) \<in> stage_rel toks rank"
      by (rule shift_stage_decreases[OF shift invariant bound])
  qed
  have reduce_case:
    "reduce_step t cfg cfg' \<Longrightarrow> (cfg', cfg) \<in> stage_rel toks rank"
  proof -
    assume reduce: "reduce_step t cfg cfg'"
    have lower_rank: "rank cfg' < rank cfg"
      using reduce_rank reduce by blast
    show "(cfg', cfg) \<in> stage_rel toks rank"
      by (rule reduce_stage_decreases[OF reduce invariant lower_rank])
  qed
  from classified show ?thesis
    by (elim disjE) (erule shift_case, erule reduce_case)
qed

lemma reachable_next_stage_decreases:
  assumes reachable: "reachable cfg"
    and invariant: "input_invariant toks cfg"
    and next_step: "one_step t cfg = Next cfg'"
    and shift_bound: "shift_step t cfg cfg' \<longrightarrow>
      position cfg < length (input_tokens cfg)"
    and reduce_rank: "reachable cfg \<Longrightarrow>
      reduce_step t cfg cfg' \<longrightarrow> rank cfg' < rank cfg"
  shows "(cfg', cfg) \<in> stage_rel toks rank"
  using reachable invariant next_step
  by (simp add: next_stage_decreases reduce_rank shift_bound)

lemma finite_execution_from_reachable:
  fixes rank :: "config \<Rightarrow> nat" and reachable::"config \<Rightarrow> bool"
  assumes init_reachable: "reachable (init_config t toks)"
    and reachable_next: "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> reachable cfg'"
    and invariant_init: "input_invariant toks (init_config t toks)"
    and invariant_next: "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> input_invariant toks cfg'"
    and shift_bound: "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      shift_step t cfg cfg' \<Longrightarrow>
        position cfg < length (input_tokens cfg)"
    and reduce_rank: "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      reduce_step t cfg cfg' \<Longrightarrow> rank cfg' < rank cfg"
  shows "\<exists>n r. run_rel t (init_config t toks) r n"
proof -
  have wf_rel: "wf (stage_rel toks rank)"
    by (simp add: stage_rel_def)
  have terminates_pre:
  "\<And>cfg. reachable cfg \<and> input_invariant toks cfg \<longrightarrow>
           (\<exists>n r. run_rel t cfg r n)"
  proof (rule wf_induct_rule[OF wf_rel])
    fix cfg x
    assume IH:"(\<And>y. (y, x) \<in> stage_rel toks rank \<Longrightarrow>
             reachable y \<and> input_invariant toks y \<longrightarrow>
             (\<exists>n r. run_rel t y r n))"
    show "reachable x \<and> input_invariant toks x \<longrightarrow> (\<exists>n r. run_rel t x r n)"
    proof
      assume a:"reachable x \<and> input_invariant toks x"
      have reachable_x: "reachable x"
        using a by simp
      have invariant_x: "input_invariant toks x"
        using a by simp
      show "\<exists>n r. run_rel t x r n"
      proof (cases "one_step t x")
        case (Next x')
        have reachable_x': "reachable x'"
          by (rule reachable_next[OF reachable_x Next])
        have invariant_x': "input_invariant toks x'"
          by (rule invariant_next[OF invariant_x Next])
        have shift_bound':
          "shift_step t x x' \<Longrightarrow>
            position x < length (input_tokens x)"
          by (auto simp add: shift_step_def)
        have reduce_rank':
          "reduce_step t x x' \<Longrightarrow> rank x' < rank x"
          using reduce_rank reachable_x by blast
        have next_step: "one_step t x = Next x'"
          using Next by blast
        have decreases: "(x', x) \<in> stage_rel toks rank"
          using invariant_x next_step reachable_next_stage_decreases reduce_rank'
            shift_bound' by auto
        obtain n r where run: "run_rel t x' r n"
          using IH decreases invariant_x' reachable_x' by blast
        have "run_rel t x r (Suc n)"
          by (rule run_rel.run_rel_next[OF Next run])
        then show ?thesis
          by (rule_tac x="Suc n" in exI, rule_tac x=r in exI, assumption)
      next
        case (Done r)
        have "run_rel t x r (Suc 0)"
          by (rule run_rel.run_rel_done[OF Done])
        then show ?thesis
          by (rule_tac x="Suc 0" in exI, rule_tac x=r in exI, assumption)
    qed
  qed
  qed
  hence terminates:
    "\<And>cfg. reachable cfg \<Longrightarrow> input_invariant toks cfg \<Longrightarrow>
      (\<exists>n r. run_rel t cfg r n)"
    by simp
  show ?thesis
    using terminates[OF init_reachable invariant_init] by blast
qed

definition finite_execution_certificate ::
  "lalr_table \<Rightarrow> token list \<Rightarrow>
  (config \<Rightarrow> bool) \<Rightarrow> (config \<Rightarrow> nat) \<Rightarrow> bool" where
  "finite_execution_certificate t toks reachable rank \<longleftrightarrow>
     reachable (init_config t toks) \<and>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       one_step t cfg = Next cfg' \<longrightarrow> reachable cfg') \<and>
     input_invariant toks (init_config t toks) \<and>
     (\<forall>cfg cfg'. input_invariant toks cfg \<longrightarrow>
       one_step t cfg = Next cfg' \<longrightarrow> input_invariant toks cfg') \<and>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       shift_step t cfg cfg' \<longrightarrow>
       position cfg < length (input_tokens cfg)) \<and>
     (\<forall>cfg cfg'. reachable cfg \<longrightarrow>
       reduce_step t cfg cfg' \<longrightarrow> rank cfg' < rank cfg)"

lemma finite_execution_certificate_of_reduce_graph:
  assumes init_reachable:
    "reachable (init_config t toks)"
    and reachable_next:
    "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> reachable cfg'"
    and invariant_init:
    "input_invariant toks (init_config t toks)"
    and invariant_next:
    "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow>
      input_invariant toks cfg'"
    and shift_bound:
    "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      shift_step t cfg cfg' \<Longrightarrow>
      position cfg < length (input_tokens cfg)"
    and reduce_correct:
    "reduce_transition_correct t"
    and reachable_source:
    "\<And>cfg. reachable cfg \<Longrightarrow>
      \<exists>toks. reachable_cfg t toks cfg"
    and graph_rank:
    "reduce_state_rank_certificate t state_rank"
  shows "finite_execution_certificate t toks reachable
    (reduce_rank_of_state state_rank)"
proof -
  have edge_certificate:
    "reduce_graph_edge_certificate reachable t"
    by (rule reduce_graph_edge_certificate_of_transition_correct
        [OF reduce_correct reachable_source])
  have rank_certificate:
    "reduce_rank_certificate reachable
      (reduce_rank_of_state state_rank) t"
    by (rule reduce_graph_rank_certificate
        [OF edge_certificate graph_rank])
  show ?thesis
    unfolding finite_execution_certificate_def
    using init_reachable reachable_next invariant_init invariant_next
      shift_bound rank_certificate
    unfolding reduce_rank_certificate_def
    by blast
qed

lemma finite_execution_certificateD:
  assumes "finite_execution_certificate t toks reachable rank"
  shows "\<exists>n r. run_rel t (init_config t toks) r n"
proof -
  have init:
    "reachable (init_config t toks)"
    using assms unfolding finite_execution_certificate_def by blast
  have reachable_next:
    "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> reachable cfg'"
    using assms unfolding finite_execution_certificate_def by blast
  have invariant_init:
    "input_invariant toks (init_config t toks)"
    using assms unfolding finite_execution_certificate_def by blast
  have invariant_next:
    "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> input_invariant toks cfg'"
    using assms unfolding finite_execution_certificate_def by blast
  have shift_bound:
    "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      shift_step t cfg cfg' \<Longrightarrow>
      position cfg < length (input_tokens cfg)"
    using assms unfolding finite_execution_certificate_def by blast
  have reduce_rank:
    "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
      reduce_step t cfg cfg' \<Longrightarrow> rank cfg' < rank cfg"
    using assms unfolding finite_execution_certificate_def by blast
  show ?thesis
    by (rule finite_execution_from_reachable
        [where reachable = reachable and rank = rank,
         OF init reachable_next invariant_init invariant_next
            shift_bound reduce_rank])
qed


definition finite_execution_target ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "finite_execution_target t toks \<longleftrightarrow>
     (\<exists>n r. run_rel t (init_config t toks) r n)"

definition termination_certificate ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "termination_certificate t toks \<longleftrightarrow>
     (\<exists>reachable rank.
        finite_execution_certificate t toks reachable rank)"

lemma termination_certificateD:
  assumes "termination_certificate t toks"
  shows "\<exists>reachable rank.
    finite_execution_certificate t toks reachable rank"
  using assms unfolding termination_certificate_def by blast

lemma termination_certificate_finite_execution:
  assumes "termination_certificate t toks"
  shows "finite_execution_target t toks"
proof -
  obtain reachable rank where certificate:
    "finite_execution_certificate t toks reachable rank"
    using termination_certificateD[OF assms] by blast
  have execution:
    "\<exists>n r. run_rel t (init_config t toks) r n"
    by (rule finite_execution_certificateD[OF certificate])
  show ?thesis
    unfolding finite_execution_target_def
    by (rule execution)
qed

locale recognizer_termination =
  fixes t :: lalr_table
    and toks :: "token list"
  assumes certificate: "termination_certificate t toks"
begin

text \<open>
  The proof is intended to use the lexicographic measure
  (remaining input length, reduction rank).  The reduction-rank part is
  represented here by well-foundedness of reduce_rel.
\<close>

lemma wf_stage_rel:
  "wf (stage_rel toks reduce_rank)"
  for reduce_rank :: "config \<Rightarrow> nat"
  by (simp add: stage_rel_def)

lemma finite_execution:
  "finite_execution_target t toks"
  by (rule termination_certificate_finite_execution[OF certificate])

text \<open>
  The finite execution theorem requires a well-founded induction over
  stage_rel.  Its induction premises are not yet available as lemmas here.
\<close>

end

end
