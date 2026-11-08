theory LALR_Termination_Schema
  imports LALR_Rank_Auto LALR_Properties
begin

text \<open>
  \textbf{A unified termination certificate for the table-driven
  recognizer.}

  Every table-specific termination proof in this development discharges the
  same six facts of @{const finite_execution_certificate}: initial
  reachability, reachability preservation, the input invariant and its
  preservation, the shift bound, and a strictly decreasing measure on reduce
  steps.  The first five follow from the table being well formed and from the
  recognizer's own definitions; only the last one depends on the table's
  grammar.  This theory proves the five generic facts once and offers two
  interchangeable suppliers for the measure obligation:

  \<^item> \<open>auto\<close>: the executable rank of @{text LALR_Rank_Auto}, generated
    from an edge list covering @{const reduce_graph} and validated by the
    decidable @{const reduce_rank_check}.  This is the right tool when the
    graph of reduce edges is acyclic.
  \<^item> \<open>height\<close>: the configuration measure
    @{text "B * |stack| + h (top)"}.  This also works when the reduce graph
    contains a cycle (for example the dangling-else table), provided that
    every reduce either pops at least two symbols, or pops exactly one and
    lowers @{text h}.

  Both suppliers are stated against the concrete reachability predicate
  @{term "reachable_cfg t toks"}, so a table needs no certificate arguments of
  its own; the per-table obligations are

  \<^enum> @{prop "wf_table t"};
  \<^enum> @{prop "end_shift_free t"};
  \<^enum> either @{prop "reduce_graph t \<subseteq> set es"} together with
    @{prop "reduce_rank_check es (auto_reduce_rank es)"} (usually by
    @{method eval}), or @{prop "height_reduce_ok t h"} together with
    @{prop "\<And>s. h s < B"}.

  The height predicate keeps the restriction on empty right-hand sides: an
  @{text \<open>\<epsilon>\<close>}-reduce keeps both the stack height and the exposed state,
  so a measure of the form @{text "B * |stack| + h (top)"} cannot decrease on
  it.  The corollary @{text height_reduce_ok_nonempty} records this formally.
\<close>

section \<open>Table obligations that are independent of the rank\<close>

text \<open>
  The input invariant only survives a step if the recognizer never shifts the
  end marker.  This is not part of @{const wf_table} (which only forbids
  accepting on a normal token), so it is stated separately.
\<close>

definition end_shift_free :: "lalr_table \<Rightarrow> bool" where
  "end_shift_free t \<longleftrightarrow> (\<forall>s st. actions t s end_token \<noteq> Some (ActShift st))"

lemma end_shift_freeD:
  assumes free: "end_shift_free t"
    and act: "actions t s end_token = Some (ActShift st)"
  shows False
  using free act unfolding end_shift_free_def by blast

text \<open>
  @{const reduce_transition_correct} is not an independent assumption for a
  well-formed table: every state of a reachable stack is a table state, and
  @{const gotos} of a well-formed table only lead to table states.
\<close>

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

lemma reduce_transition_correctI:
  assumes wf: "wf_table t"
  shows "reduce_transition_correct t"
  unfolding reduce_transition_correct_def
proof (intro allI impI)
  fix toks cfg cfg' s g
  assume rt: "reduce_transition t toks cfg cfg' s g"
  have reach: "reachable_cfg t toks cfg"
    using rt unfolding reduce_transition_def by blast
  have step: "reduce_transition_step t cfg cfg' s g"
    using rt unfolding reduce_transition_def by blast
  have stack_states: "set (state_stack cfg) \<subseteq> states t"
    by (rule reachable_cfg_stack_states[OF wf reach])
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
  have act: "actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid)"
    using dec by blast
  have prod: "productions t rid = Some p"
    using dec by blast
  have pop: "pop_rhs (length (rhs p)) (state_stack cfg) = Some stk'"
    using dec by blast
  have tops': "top_state stk' = Some s'"
    using dec by blast
  have goto: "gotos t s' (lhs p) = Some g"
    using dec by blast
  have g_states: "g \<in> states t"
    using wf goto unfolding wf_table_def by blast
  have subset: "set stk' \<subseteq> set (state_stack cfg)"
    by (rule pop_rhs_subset[OF pop])
  have s'_states: "s' \<in> states t"
    using tops' subset stack_states top_state_member by blast
  show "s \<in> states t \<and> g \<in> states t \<and>
    (\<exists>tok rid p s'.
      actions t s tok = Some (ActReduce rid) \<and>
      productions t rid = Some p \<and>
      s' \<in> states t \<and>
      gotos t s' (lhs p) = Some g)"
  proof (intro conjI)
    show "s \<in> states t" by (rule s_states)
  next
    show "g \<in> states t" by (rule g_states)
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

section \<open>Generic reduction-step structure\<close>

lemma pop_rhs_length_add:
  "pop_rhs n stk = Some stk' \<Longrightarrow> length stk' + n = length stk"
proof -
  assume pop: "pop_rhs n stk = Some stk'"
  have n_lt: "n < length stk"
    using pop unfolding pop_rhs_def by (auto split: if_splits)
  have eq: "length stk' = length stk - n"
    by (rule pop_rhs_some_length[OF pop])
  from eq n_lt show ?thesis by arith
qed

lemma reduce_step_position:
  assumes "reduce_step t cfg cfg'"
  shows "position cfg' = position cfg"
  using assms unfolding reduce_step_def
  by (auto simp: one_step_def append_trace_def split: option.splits action.splits)

text \<open>
  A reduce step is completely described by its lookahead state, its
  production, the stack below the handle, the state it exposes, the goto
  target and the resulting stack.  This is the single decomposition lemma all
  rank arguments below are built on.
\<close>

lemma reduce_step_stack_decomposition:
  assumes step: "reduce_step t cfg cfg'"
  shows "\<exists>s rid p stk' s' g.
      top_state (state_stack cfg) = Some s \<and>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<and>
      productions t rid = Some p \<and>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
      top_state stk' = Some s' \<and>
      gotos t s' (lhs p) = Some g \<and>
      state_stack cfg' = stk' @ [g]"
proof -
  from reduce_step_obtain[OF step] obtain s rid where
    pos: "position cfg < length (input_tokens cfg)"
    and top: "top_state (state_stack cfg) = Some s"
    and act: "actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid)"
    and nxt: "one_step t cfg = Next cfg'"
    by blast
  have dec: "\<exists>p stk' s' g. productions t rid = Some p \<and>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
      top_state stk' = Some s' \<and>
      gotos t s' (lhs p) = Some g \<and>
      state_stack cfg' = stk' @ [g]"
    using pos top act nxt
    unfolding one_step_def Let_def
    by (auto simp: append_trace_def split: option.splits action.splits if_splits)
  then obtain p stk' s' g where
    prod: "productions t rid = Some p"
    and pop: "pop_rhs (length (rhs p)) (state_stack cfg) = Some stk'"
    and tops': "top_state stk' = Some s'"
    and goto: "gotos t s' (lhs p) = Some g"
    and stack: "state_stack cfg' = stk' @ [g]"
    by blast
  show ?thesis
    by (rule_tac x=s in exI, rule_tac x=rid in exI, rule_tac x=p in exI,
        rule_tac x=stk' in exI, rule_tac x=s' in exI, rule_tac x=g in exI,
        intro conjI, rule top, rule act, rule prod, rule pop, rule tops',
        rule goto, rule stack)
qed

section \<open>The five generic certificate facts\<close>

text \<open>
  This is the heart of the unified format: <em>one</em> lemma turns the
  table-independent part of the obligation into the certificate, leaving the
  caller with a single measure-decrease proof.
\<close>

lemma finite_execution_certificateI:
  assumes init_reachable: "reachable (init_config t toks)"
    and reachable_next:
      "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
        one_step t cfg = Next cfg' \<Longrightarrow> reachable cfg'"
    and invariant_init: "input_invariant toks (init_config t toks)"
    and invariant_next:
      "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
        one_step t cfg = Next cfg' \<Longrightarrow> input_invariant toks cfg'"
    and shift_bound:
      "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
        shift_step t cfg cfg' \<Longrightarrow>
        position cfg < length (input_tokens cfg)"
    and reduce_decrease:
      "\<And>cfg cfg'. reachable cfg \<Longrightarrow>
        reduce_step t cfg cfg' \<Longrightarrow> rank cfg' < rank cfg"
  shows "finite_execution_certificate t toks reachable rank"
  unfolding finite_execution_certificate_def
  using assms by blast

text \<open>
  The input invariant is preserved by any step of a table that never shifts
  the end marker.  This replaces the per-table case analysis on the action of
  @{const one_step} that every table used to repeat.
\<close>

lemma input_invariant_stepI:
  assumes inv: "input_invariant toks cfg"
    and step: "one_step t cfg = Next cfg'"
    and free: "end_shift_free t"
  shows "input_invariant toks cfg'"
proof (cases "position cfg < length toks")
  case True
  have frame: "input_tokens cfg' = input_tokens cfg \<and>
      (position cfg' = position cfg \<or> position cfg' = Suc (position cfg))"
    by (rule one_step_next_input_frame[OF step])
  from frame have frame_tok: "input_tokens cfg' = input_tokens cfg"
    and frame_pos: "position cfg' = position cfg \<or> position cfg' = Suc (position cfg)"
    by blast+
  from inv have tok: "input_tokens cfg = toks @ [end_token]"
    and pos: "position cfg \<le> length toks"
    unfolding input_invariant_def by blast+
  show ?thesis
    unfolding input_invariant_def
  proof
    show "input_tokens cfg' = toks @ [end_token]" using frame_tok tok by simp
  next
    show "position cfg' \<le> length toks" using frame_pos pos True by auto
  qed
next
  case False
  with inv have eq: "position cfg = length toks"
    unfolding input_invariant_def by simp
  have tok: "input_tokens cfg = toks @ [end_token]"
    using inv unfolding input_invariant_def by blast
  have frame_tok: "input_tokens cfg' = input_tokens cfg"
    using one_step_next_input_frame[OF step] by blast
  have la: "input_tokens cfg ! position cfg = end_token"
  proof -
    have same: "input_tokens cfg ! position cfg = (toks @ [end_token]) ! length toks"
      using tok eq by simp
    have last: "(toks @ [end_token]) ! length toks = end_token"
      by (rule nth_append_length)
    from same last show ?thesis by simp
  qed
  have no_shift: "\<not> shift_step t cfg cfg'"
  proof
    assume shift: "shift_step t cfg cfg'"
    then obtain s st where
      act: "actions t s (input_tokens cfg ! position cfg) = Some (ActShift st)"
      unfolding shift_step_def by blast
    have "actions t s end_token = Some (ActShift st)" using act la by simp
    then show False by (rule end_shift_freeD[OF free])
  qed
  have red: "reduce_step t cfg cfg'"
    using next_is_shift_or_reduce[OF step] no_shift by blast
  have pos': "position cfg' = position cfg"
    by (rule reduce_step_position[OF red])
  show ?thesis
    unfolding input_invariant_def
  proof
    show "input_tokens cfg' = toks @ [end_token]" using frame_tok tok by simp
  next
    show "position cfg' \<le> length toks" using pos' eq by simp
  qed
qed

section \<open>The two measure shapes\<close>

text \<open>
  The state-only rank of the theory @{text LALR_Rank_Auto}.  The generated rank is
  validated by the decidable checker, so the caller never states a rank
  function by hand.
\<close>

theorem finite_execution_certificate_auto:
  assumes free: "end_shift_free t"
    and correct: "reduce_transition_correct t"
    and edges: "reduce_graph t \<subseteq> set es"
    and check: "reduce_rank_check es (auto_reduce_rank es)"
  shows "finite_execution_certificate t toks (reachable_cfg t toks)
    (reduce_rank_of_state (auto_reduce_rank es))"
proof (rule finite_execution_certificate_of_reduce_graph_auto
    [where reachable = "reachable_cfg t toks"])
  show "reachable_cfg t toks (init_config t toks)"
    by (rule reachable_cfg_init)
next
  show "\<And>cfg cfg'. reachable_cfg t toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> reachable_cfg t toks cfg'"
    by (rule reachable_cfg_next)
next
  show "input_invariant toks (init_config t toks)"
    by (rule input_invariant_init)
next
  show "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> input_invariant toks cfg'"
    by (rule input_invariant_stepI[OF _ _ free])
next
  show "\<And>cfg cfg'. reachable_cfg t toks cfg \<Longrightarrow>
      shift_step t cfg cfg' \<Longrightarrow> position cfg < length (input_tokens cfg)"
    by (auto simp: shift_step_def)
next
  show "reduce_transition_correct t" by (rule correct)
next
  show "\<And>cfg. reachable_cfg t toks cfg \<Longrightarrow> \<exists>toks'. reachable_cfg t toks' cfg"
    by (rule_tac x=toks in exI, assumption)
next
  show "reduce_graph t \<subseteq> set es" by (rule edges)
next
  show "reduce_rank_check es (auto_reduce_rank es)" by (rule check)
qed

text \<open>
  The height-based measure.  @{term "height_reduce_ok t h"} is the whole
  table-specific content: every reduce either pops at least two symbols (so
  that the stack shrinks even if @{text h} grows), or pops one symbol and
  strictly lowers @{text h}.  A reduce with an empty right-hand side is
  excluded, because it never shrinks the stack; such a table needs a different
  measure.
\<close>

definition height_rank :: "nat \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> config \<Rightarrow> nat" where
  "height_rank B h cfg = B * length (state_stack cfg) + reduce_rank_of_state h cfg"

definition height_reduce_ok :: "lalr_table \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> bool" where
  "height_reduce_ok t h \<longleftrightarrow>
     (\<forall>s tok rid p s' g.
        actions t s tok = Some (ActReduce rid) \<longrightarrow>
        productions t rid = Some p \<longrightarrow>
        gotos t s' (lhs p) = Some g \<longrightarrow>
        2 \<le> length (rhs p) \<or> (length (rhs p) = 1 \<and> h g < h s))"

lemma height_reduce_okD:
  assumes ok: "height_reduce_ok t h"
    and act: "actions t s tok = Some (ActReduce rid)"
    and prod: "productions t rid = Some p"
    and goto: "gotos t s' (lhs p) = Some g"
  shows "2 \<le> length (rhs p) \<or> (length (rhs p) = 1 \<and> h g < h s)"
  using ok act prod goto unfolding height_reduce_ok_def by blast

lemma height_reduce_ok_nonempty:
  assumes ok: "height_reduce_ok t h"
    and act: "actions t s tok = Some (ActReduce rid)"
    and prod: "productions t rid = Some p"
    and goto: "gotos t s' (lhs p) = Some g"
  shows "0 < length (rhs p)"
  using height_reduce_okD[OF ok act prod goto] by arith

text \<open>
  The exclusion of empty right-hand sides is part of the interface: an
  @{text \<open>\<epsilon>\<close>}-reduce neither shrinks the stack nor changes the exposed state,
  so no measure built from the stack shape can decrease on it.  The corollary
  above records that @{const height_reduce_ok} rules such reductions out.
\<close>

text \<open>
  Arithmetic of the encoding @{term "B * n + r"} with @{prop "r < B"}:
  a smaller stack height dominates, and equal heights are decided by the
  state part.
\<close>

lemma encoded_less_le:
  fixes m n B a b :: nat
  assumes mn: "m < n" and aB: "a < B"
  shows "B * m + a < B * n + b"
proof -
  have succ: "m + 1 \<le> n" using mn by simp
  have "B * m + a < B * m + B" using aB by arith
  also have "\<dots> = B * (m + 1)" by (simp add: algebra_simps)
  also have "\<dots> \<le> B * n" by (rule mult_le_mono2, rule succ)
  also have "\<dots> \<le> B * n + b" by simp
  finally show ?thesis .
qed

lemma height_rank_less_shorter:
  assumes shorter: "length (state_stack cfg') < length (state_stack cfg)"
    and bound: "reduce_rank_of_state h cfg' < B"
  shows "height_rank B h cfg' < height_rank B h cfg"
  unfolding height_rank_def
  by (rule encoded_less_le[OF shorter bound])

lemma height_rank_less_same_length:
  assumes same: "length (state_stack cfg') = length (state_stack cfg)"
    and dec: "reduce_rank_of_state h cfg' < reduce_rank_of_state h cfg"
  shows "height_rank B h cfg' < height_rank B h cfg"
proof -
  have "B * length (state_stack cfg') + reduce_rank_of_state h cfg' <
        B * length (state_stack cfg') + reduce_rank_of_state h cfg"
    using dec by arith
  also have "\<dots> = B * length (state_stack cfg) + reduce_rank_of_state h cfg"
    using same by simp
  finally show ?thesis by (simp add: height_rank_def)
qed

text \<open>
  The single measure-decrease lemma of the height route: it is the only place
  where the decomposition of a reduce step is used.
\<close>

lemma reduce_step_height_decrease:
  assumes step: "reduce_step t cfg cfg'"
    and ok: "height_reduce_ok t h"
    and bound: "\<And>s. h s < B"
  shows "height_rank B h cfg' < height_rank B h cfg"
proof -
  from reduce_step_stack_decomposition[OF step] obtain s rid p stk' s' g where
    top: "top_state (state_stack cfg) = Some s"
    and act: "actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid)"
    and prod: "productions t rid = Some p"
    and pop: "pop_rhs (length (rhs p)) (state_stack cfg) = Some stk'"
    and tops': "top_state stk' = Some s'"
    and goto: "gotos t s' (lhs p) = Some g"
    and stack: "state_stack cfg' = stk' @ [g]"
    by blast
  have len_add: "length stk' + length (rhs p) = length (state_stack cfg)"
    by (rule pop_rhs_length_add[OF pop])
  have len': "length (state_stack cfg') = Suc (length stk')"
    using stack by simp
  have top': "top_state (state_stack cfg') = Some g"
    using stack unfolding top_state_def by simp
  have rank': "reduce_rank_of_state h cfg' = h g"
    using top' unfolding reduce_rank_of_state_def by simp
  have rank: "reduce_rank_of_state h cfg = h s"
    using top unfolding reduce_rank_of_state_def by simp
  have cases: "2 \<le> length (rhs p) \<or> (length (rhs p) = 1 \<and> h g < h s)"
    by (rule height_reduce_okD[OF ok act prod goto])
  from cases show ?thesis
  proof
    assume big: "2 \<le> length (rhs p)"
    have shorter: "length (state_stack cfg') < length (state_stack cfg)"
    proof -
      have "length stk' + 2 \<le> length (state_stack cfg)"
        using len_add big by arith
      with len' show ?thesis by arith
    qed
    have bound': "reduce_rank_of_state h cfg' < B"
      using rank' bound[of g] by simp
    show ?thesis by (rule height_rank_less_shorter[OF shorter bound'])
  next
    assume unit: "length (rhs p) = 1 \<and> h g < h s"
    have rhs_one: "length (rhs p) = 1" using unit by simp
    have lower: "h g < h s" using unit by simp
    have same: "length (state_stack cfg') = length (state_stack cfg)"
    proof -
      have "length stk' + 1 = length (state_stack cfg)"
        using len_add rhs_one by simp
      with len' show ?thesis by arith
    qed
    have dec: "reduce_rank_of_state h cfg' < reduce_rank_of_state h cfg"
      using rank rank' lower by simp
    show ?thesis by (rule height_rank_less_same_length[OF same dec])
  qed
qed

theorem finite_execution_certificate_height:
  assumes free: "end_shift_free t"
    and ok: "height_reduce_ok t h"
    and bound: "\<And>s. h s < B"
  shows "finite_execution_certificate t toks (reachable_cfg t toks) (height_rank B h)"
proof (rule finite_execution_certificateI)
  show "reachable_cfg t toks (init_config t toks)"
    by (rule reachable_cfg_init)
next
  show "\<And>cfg cfg'. reachable_cfg t toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> reachable_cfg t toks cfg'"
    by (rule reachable_cfg_next)
next
  show "input_invariant toks (init_config t toks)"
    by (rule input_invariant_init)
next
  show "\<And>cfg cfg'. input_invariant toks cfg \<Longrightarrow>
      one_step t cfg = Next cfg' \<Longrightarrow> input_invariant toks cfg'"
    by (rule input_invariant_stepI[OF _ _ free])
next
  show "\<And>cfg cfg'. reachable_cfg t toks cfg \<Longrightarrow>
      shift_step t cfg cfg' \<Longrightarrow> position cfg < length (input_tokens cfg)"
    by (auto simp: shift_step_def)
next
  show "\<And>cfg cfg'. reachable_cfg t toks cfg \<Longrightarrow>
      reduce_step t cfg cfg' \<Longrightarrow> height_rank B h cfg' < height_rank B h cfg"
    by (rule reduce_step_height_decrease[OF _ ok bound])
qed

section \<open>Unified per-table interface\<close>

text \<open>
  Two suppliers, each already existentially closed over @{const reachable_cfg}
  and the measure, so a table concludes @{const termination_certificate}
  directly.  The auto route hides transition correctness behind @{const
  wf_table}; the height route hides the encoding arithmetic behind @{const
  height_rank}.  Everything else (@{const finite_execution_target}, finite
  @{text run_rel} runs) follows from the framework corollaries
  @{thm [source] termination_certificate_finite_execution} and
  @{thm [source] finite_execution_certificateD}.
\<close>

theorem termination_certificate_auto:
  assumes wf: "wf_table t"
    and free: "end_shift_free t"
    and edges: "reduce_graph t \<subseteq> set es"
    and check: "reduce_rank_check es (auto_reduce_rank es)"
  shows "termination_certificate t toks"
  unfolding termination_certificate_def
  using finite_execution_certificate_auto
    [OF free reduce_transition_correctI[OF wf] edges check]
  by blast

theorem termination_certificate_height:
  assumes free: "end_shift_free t"
    and ok: "height_reduce_ok t h"
    and bound: "\<And>s. h s < B"
  shows "termination_certificate t toks"
  unfolding termination_certificate_def
  using finite_execution_certificate_height[OF free ok bound]
  by blast

text \<open>
  A single statement covering both suppliers: a well-formed table that never
  shifts the end marker and carries either rank certificate terminates on
  every input.
\<close>

theorem termination_certificate_cases:
  assumes wf: "wf_table t"
    and free: "end_shift_free t"
    and rank_certificate:
      "(reduce_graph t \<subseteq> set es \<and> reduce_rank_check es (auto_reduce_rank es)) \<or>
       (height_reduce_ok t h \<and> (\<forall>s. h s < B))"
  shows "termination_certificate t toks"
proof -
  from rank_certificate show ?thesis
  proof
    assume auto: "reduce_graph t \<subseteq> set es \<and>
        reduce_rank_check es (auto_reduce_rank es)"
    from auto have edges: "reduce_graph t \<subseteq> set es"
      and check: "reduce_rank_check es (auto_reduce_rank es)"
      by blast+
    show ?thesis by (rule termination_certificate_auto[OF wf free edges check])
  next
    assume height: "height_reduce_ok t h \<and> (\<forall>s. h s < B)"
    from height have ok: "height_reduce_ok t h"
      and bound: "\<forall>s. h s < B"
      by blast+
    show ?thesis
      by (rule termination_certificate_height[where B = B, OF free ok],
          simp add: bound)
  qed
qed

theorem finite_execution_target_cases:
  assumes wf: "wf_table t"
    and free: "end_shift_free t"
    and rank_certificate:
      "(reduce_graph t \<subseteq> set es \<and> reduce_rank_check es (auto_reduce_rank es)) \<or>
       (height_reduce_ok t h \<and> (\<forall>s. h s < B))"
  shows "finite_execution_target t toks"
  using termination_certificate_finite_execution
    [OF termination_certificate_cases[OF wf free rank_certificate]] .

end
