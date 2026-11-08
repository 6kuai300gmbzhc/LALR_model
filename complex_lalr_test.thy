theory complex_lalr_test
  imports LALR_Termination LALR_Stack LALR_Rank_Auto LALR_Termination_Schema
begin

text \<open>
    state 214 --(244: Expr -> Tempo_expr)--> state 344
    state 344 --(264: Tempo_expr -> PRE Expr)--> state 214
\<close>

definition complex_p244 :: production where
  "complex_p244 =
    \<lparr>number = 244, lhs = ''Expr'',
      rhs = [Nonterminal ''Tempo_expr'']\<rparr>"

definition complex_p264 :: production where
  "complex_p264 =
    \<lparr>number = 264, lhs = ''Tempo_expr'',
      rhs = [Terminal ''PRE'', Nonterminal ''Expr'']\<rparr>"

definition complex_cfg :: "symbol cfg" where
  "complex_cfg =
    CFG [(''Expr'', [Nonterminal ''Tempo_expr'']),
         (''Tempo_expr'', [Terminal ''PRE'', Nonterminal ''Expr''])]
      ''Expr''"

definition complex_productions ::
  "production_id \<Rightarrow> production option" where
  "complex_productions n =
    map_of [(244, complex_p244), (264, complex_p264)] n"

definition complex_actions :: "state \<Rightarrow> token \<Rightarrow> action option" where
  "complex_actions s tok =
    map_of [((214, ''ARROW''), ActReduce 244),
            ((344, ''ARROW''), ActReduce 264)] (s, tok)"

definition complex_gotos ::
  "state \<Rightarrow> nonterminal_ \<Rightarrow> state option" where
  "complex_gotos s nt =
    map_of [((233, ''Expr''), 344),
            ((233, ''Tempo_expr''), 214)] (s, nt)"

definition complex_table :: lalr_table where
  "complex_table =
    \<lparr>parsing_method = ''LALR'',
      terminals = {''PRE'', ''ID'', ''ARROW'', end_token},
      nonterminals = {''Expr'', ''Tempo_expr''},
      states = {214, 233, 344},
      productions = complex_productions,
      actions = complex_actions,
      gotos = complex_gotos,
      start_state = 233\<rparr>"

definition complex_reduce_edges :: "(state \<times> state) set" where
  "complex_reduce_edges = {(214, 344), (344, 214)}"

lemma complex_wf_table: "wf_table complex_table"
  unfolding wf_table_def complex_table_def
    complex_actions_def complex_productions_def complex_gotos_def
  by (auto split: if_splits prod.splits)

lemma complex_reduce_actions:
  "actions complex_table s tok = Some (ActReduce rid) \<Longrightarrow>
   (s = 214 \<and> rid = 244) \<or> (s = 344 \<and> rid = 264)"
  unfolding complex_table_def complex_actions_def
  by (auto split: if_splits prod.splits)

lemma complex_productions_244 [simp]:
  "productions complex_table 244 = Some complex_p244"
  by (simp add: complex_table_def complex_productions_def)

lemma complex_productions_264 [simp]:
  "productions complex_table 264 = Some complex_p264"
  by (simp add: complex_table_def complex_productions_def)

lemma complex_goto_expr:
  "gotos complex_table s ''Expr'' = Some g \<Longrightarrow> g = 344"
  unfolding complex_table_def complex_gotos_def
  by (auto split: if_splits prod.splits)

lemma complex_goto_tempo:
  "gotos complex_table s ''Tempo_expr'' = Some g \<Longrightarrow> g = 214"
  unfolding complex_table_def complex_gotos_def
  by (auto split: if_splits prod.splits)

lemma complex_reduce_cycle_edges:
  "(214, 344) \<in> reduce_graph complex_table"
  "(344, 214) \<in> reduce_graph complex_table"
proof -
  have state_214: "214 \<in> states complex_table"
    and state_344: "344 \<in> states complex_table"
    by (simp_all add: complex_table_def)
  have witness_244:
    "\<exists>tok rid p s'. actions complex_table 214 tok = Some (ActReduce rid) \<and>
      productions complex_table rid = Some p \<and>
      s' \<in> states complex_table \<and>
      gotos complex_table s' (lhs p) = Some 344"
    by (rule_tac x="''ARROW''" in exI,
        rule_tac x=244 in exI,
        rule_tac x=complex_p244 in exI,
        rule_tac x=233 in exI,
        simp add: complex_table_def complex_actions_def
          complex_productions_def complex_gotos_def complex_p244_def)
  have witness_264:
    "\<exists>tok rid p s'. actions complex_table 344 tok = Some (ActReduce rid) \<and>
      productions complex_table rid = Some p \<and>
      s' \<in> states complex_table \<and>
      gotos complex_table s' (lhs p) = Some 214"
    by (rule_tac x="''ARROW''" in exI,
        rule_tac x=264 in exI,
        rule_tac x=complex_p264 in exI,
        rule_tac x=233 in exI,
        simp add: complex_table_def complex_actions_def
          complex_productions_def complex_gotos_def complex_p264_def)
  show "(214, 344) \<in> reduce_graph complex_table"
    using state_214 state_344 witness_244
    unfolding reduce_graph_def by blast
  show "(344, 214) \<in> reduce_graph complex_table"
    using state_344 state_214 witness_264
    unfolding reduce_graph_def by blast
qed

lemma complex_reduce_graph_subset:
  "reduce_graph complex_table \<subseteq> complex_reduce_edges"
proof (rule subsetI)
  fix edge
  assume edge: "edge \<in> reduce_graph complex_table"
  then obtain s g where pair: "edge = (s, g)"
    by (cases edge) auto
  have edge_pair: "(s, g) \<in> reduce_graph complex_table"
    using edge pair by simp
  from edge_pair obtain tok rid p s' where dec:
    "s \<in> states complex_table"
    "actions complex_table s tok = Some (ActReduce rid)"
    "productions complex_table rid = Some p"
    "s' \<in> states complex_table"
    "gotos complex_table s' (lhs p) = Some g"
    "g \<in> states complex_table"
    unfolding reduce_graph_def by blast
  from complex_reduce_actions[OF dec(2)]
  consider (expr) "s = 214" "rid = 244"
    | (tempo) "s = 344" "rid = 264"
    by blast
  then have "(s, g) \<in> complex_reduce_edges"
  proof cases
    case expr
    have "p = complex_p244"
      using dec(3) expr by (simp add: complex_productions_def)
    then have "lhs p = ''Expr''"
      by (simp add: complex_p244_def)
    have goto_expr: "gotos complex_table s' ''Expr'' = Some g"
      using dec(5) \<open>lhs p = ''Expr''\<close> by simp
    have "g = 344" by (rule complex_goto_expr[OF goto_expr])
    with expr show ?thesis
      by (simp add: complex_reduce_edges_def)
  next
    case tempo
    have "p = complex_p264"
      using dec(3) tempo by (simp add: complex_productions_def)
    then have "lhs p = ''Tempo_expr''"
      by (simp add: complex_p264_def)
    have goto_tempo: "gotos complex_table s' ''Tempo_expr'' = Some g"
      using dec(5) \<open>lhs p = ''Tempo_expr''\<close> by simp
    have "g = 214" by (rule complex_goto_tempo[OF goto_tempo])
    with tempo show ?thesis
      by (simp add: complex_reduce_edges_def)
  qed
  with pair show "edge \<in> complex_reduce_edges" by simp
qed

lemma complex_reduce_graph_not_acyclic:
  "\<not> acyclic (reduce_graph complex_table)"
proof
  assume acyclic: "acyclic (reduce_graph complex_table)"
  then have no_cycle:
    "\<forall>s. (s, s) \<notin> (reduce_graph complex_table)\<^sup>+"
    unfolding acyclic_def .
  have "(214, 214) \<in> (reduce_graph complex_table)\<^sup>+"
    using complex_reduce_cycle_edges by (meson trancl.intros)
  with no_cycle show False by blast
qed

lemma complex_no_state_reduce_rank:
  "\<not> (\<exists>rank :: state \<Rightarrow> nat.
      reduce_state_rank_certificate complex_table rank)"
proof
  assume "\<exists>rank :: state \<Rightarrow> nat.
      reduce_state_rank_certificate complex_table rank"
  then obtain rank :: "state \<Rightarrow> nat" where
    certificate:
      "reduce_state_rank_certificate complex_table rank"
    by blast
  have down: "rank 344 < rank 214"
    using reduce_graph_rank_decreases[OF certificate]
      complex_reduce_cycle_edges(1) by blast
  have up: "rank 214 < rank 344"
    using reduce_graph_rank_decreases[OF certificate]
      complex_reduce_cycle_edges(2) by blast
  from down up show False by simp
qed

text \<open>
  The one-symbol reduction 244 lowers the exposed-state weight from 1 to 0.
  Reduction 264 pops two symbols, so it lowers the stack-height component
  regardless of the exposed-state weight.
\<close>

definition complex_height :: "state \<Rightarrow> nat" where
  "complex_height s = (if s = 214 then 1 else 0)"

lemma complex_height_bound: "complex_height s < 2"
  by (simp add: complex_height_def)

lemma complex_end_shift_free: "end_shift_free complex_table"
  unfolding end_shift_free_def complex_table_def complex_actions_def
  by (auto split: if_splits prod.splits)

lemma complex_height_reduce_ok:
  "height_reduce_ok complex_table complex_height"
  unfolding height_reduce_ok_def
proof (intro allI impI)
  fix s tok rid p s' g
  assume action:
    "actions complex_table s tok = Some (ActReduce rid)"
    and production: "productions complex_table rid = Some p"
    and goto: "gotos complex_table s' (lhs p) = Some g"
  from complex_reduce_actions[OF action]
  consider (expr) "s = 214" "rid = 244"
    | (tempo) "s = 344" "rid = 264"
    by blast
  then show
    "2 \<le> length (rhs p) \<or>
     (length (rhs p) = 1 \<and> complex_height g < complex_height s)"
  proof cases
    case expr
    have p_eq: "p = complex_p244"
      using production expr by (simp add: complex_productions_def)
    have lhs_eq: "lhs p = ''Expr''"
      using p_eq by (simp add: complex_p244_def)
    have goto_expr: "gotos complex_table s' ''Expr'' = Some g"
      using goto lhs_eq by simp
    have target: "g = 344"
      by (rule complex_goto_expr[OF goto_expr])
    show ?thesis
      using expr target p_eq
      by (simp add: complex_height_def complex_p244_def)
  next
    case tempo
    have p_eq: "p = complex_p264"
      using production tempo by (simp add: complex_productions_def)
    show ?thesis
      using p_eq by (simp add: complex_p264_def)
  qed
qed

lemma complex_termination_certificate:
  "termination_certificate complex_table toks"
  by (rule termination_certificate_height
      [OF complex_end_shift_free complex_height_reduce_ok
        complex_height_bound])

theorem complex_lalr_termination:
  "finite_execution_target complex_table toks"
  by (rule termination_certificate_finite_execution
      [OF complex_termination_certificate])

corollary complex_lalr_terminates:
  "\<exists>n r. run_rel complex_table (init_config complex_table toks) r n"
  using complex_lalr_termination
  unfolding finite_execution_target_def .

text \<open>
  As in the other test tables, the executable rank generator is run on the
  edge list of this table to show that it cannot certify it: the reduction
  graph has the cycle @{text "214 \<rightarrow> 344 \<rightarrow> 214"}, so at the fixed point the
  two states carry the same value and the edge @{text "(214, 344)"} cannot
  decrease.  The generator is still executable on this input, which is what
  the @{text eval} lemmas below record.
\<close>

definition complex_reduce_edge_list :: "(state \<times> state) list" where
  "complex_reduce_edge_list = [(214, 344), (344, 214)]"

lemma complex_edges_set_eq:
  "set complex_reduce_edge_list = complex_reduce_edges"
  by (simp add: complex_reduce_edge_list_def complex_reduce_edges_def)

lemma complex_generated_rank_check_fails:
  "\<not> reduce_rank_check complex_reduce_edge_list
      (auto_reduce_rank complex_reduce_edge_list)"
  by eval

lemma complex_generated_rank_values:
  "auto_reduce_rank complex_reduce_edge_list 214 = 3"
  "auto_reduce_rank complex_reduce_edge_list 344 = 3"
  by eval+

text \<open>
  The unified entry point of the termination schema, instantiated with the
  second (height) case of its disjunction: one rule application plus the two
  height obligations replaces the direct application of
  @{thm [source] termination_certificate_height}.
\<close>

theorem complex_termination_certificate_cases:
  "termination_certificate complex_table toks"
  by (rule termination_certificate_cases
      [OF complex_wf_table complex_end_shift_free],
      rule disjI2, intro conjI,
      rule complex_height_reduce_ok, rule allI, rule complex_height_bound)

end
