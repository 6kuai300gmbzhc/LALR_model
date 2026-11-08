theory lalr_if_test
  imports LALR_Termination LALR_Stack LALR_Rank_Auto LALR_Termination_Schema
begin

text \<open>
  A small LALR model extracted from the dangling-else productions.  Its
  state-only reduce graph contains the cycle 7 \<rightarrow> 9 \<rightarrow> 7.
\<close>

definition if_p0 :: production where
  "if_p0 = \<lparr>number = 0, lhs = ''S'', rhs = [Nonterminal ''Start'']\<rparr>"

definition if_p1 :: production where
  "if_p1 = \<lparr>number = 1, lhs = ''Start'', rhs = [Nonterminal ''IfBlock'']\<rparr>"

definition if_p2 :: production where
  "if_p2 = \<lparr>number = 2, lhs = ''IfBlock'',
    rhs = [Terminal ''IF'', Terminal ''ID'', Terminal ''THEN'',
      Nonterminal ''ElseClause'']\<rparr>"

definition if_p3 :: production where
  "if_p3 = \<lparr>number = 3, lhs = ''ElseClause'',
    rhs = [Terminal ''ELSE'', Nonterminal ''IfBlock'']\<rparr>"

definition if_p4 :: production where
  "if_p4 = \<lparr>number = 4, lhs = ''ElseClause'',
    rhs = [Terminal ''ELSE'', Terminal ''ID'']\<rparr>"

definition if_cfg :: "symbol cfg" where
  "if_cfg = CFG [
    (''Start'', [Nonterminal ''IfBlock'']),
    (''IfBlock'', [Terminal ''IF'', Terminal ''ID'', Terminal ''THEN'',
      Nonterminal ''ElseClause'']),
    (''ElseClause'', [Terminal ''ELSE'', Nonterminal ''IfBlock'']),
    (''ElseClause'', [Terminal ''ELSE'', Terminal ''ID''])] ''Start''"

definition if_productions :: "production_id \<Rightarrow> production option" where
  "if_productions n =
    map_of [(0, if_p0), (1, if_p1), (2, if_p2), (3, if_p3), (4, if_p4)] n"

definition if_actions :: "state \<Rightarrow> token \<Rightarrow> action option" where
  "if_actions s tok = map_of [
    ((0, ''IF''), ActShift 3),
    ((1, ''END''), ActAccept),
    ((2, ''END''), ActReduce 1),
    ((3, ''ID''), ActShift 4),
    ((4, ''THEN''), ActShift 5),
    ((5, ''ELSE''), ActShift 6),
    ((6, ''IF''), ActShift 3),
    ((6, ''ID''), ActShift 8),
    ((7, ''END''), ActReduce 3),
    ((8, ''END''), ActReduce 4),
    ((9, ''END''), ActReduce 2)] (s, tok)"

definition if_gotos :: "state \<Rightarrow> nonterminal_ \<Rightarrow> state option" where
  "if_gotos s nt = map_of [
    ((0, ''Start''), 1),
    ((0, ''IfBlock''), 2),
    ((5, ''ElseClause''), 9),
    ((6, ''IfBlock''), 7)] (s, nt)"

definition if_table :: lalr_table where
  "if_table =
    \<lparr>parsing_method = ''LALR'',
      terminals = {''IF'', ''ID'', ''THEN'', ''ELSE'', end_token},
      nonterminals = {''S'', ''Start'', ''IfBlock'', ''ElseClause''},
      states = {0..9},
      productions = if_productions,
      actions = if_actions,
      gotos = if_gotos,
      start_state = 0\<rparr>"

definition if_reduce_edges :: "(state \<times> state) set" where
  "if_reduce_edges =
    {(2, 1), (7, 9), (8, 9), (9, 2), (9, 7)}"

definition if_reduce_edge_list :: "(state \<times> state) list" where
  "if_reduce_edge_list = [(2, 1), (7, 9), (8, 9), (9, 2), (9, 7)]"

definition if_auto_reduce_rank :: "state \<Rightarrow> nat" where
  "if_auto_reduce_rank = auto_reduce_rank if_reduce_edge_list"

text \<open>Facts about the five productions of the table.\<close>

lemma if_rule_1 [simp]:
  "lhs if_p1 = ''Start''" "length (rhs if_p1) = 1"
  by (simp_all add: if_p1_def)

lemma if_rule_2 [simp]:
  "lhs if_p2 = ''IfBlock''" "length (rhs if_p2) = 4"
  by (simp_all add: if_p2_def)

lemma if_rule_3 [simp]:
  "lhs if_p3 = ''ElseClause''" "length (rhs if_p3) = 2"
  by (simp_all add: if_p3_def)

lemma if_rule_4 [simp]:
  "lhs if_p4 = ''ElseClause''" "length (rhs if_p4) = 2"
  by (simp_all add: if_p4_def)

lemma if_productions_1 [simp]: "productions if_table 1 = Some if_p1"
  by (simp add: if_table_def if_productions_def)

lemma if_productions_2 [simp]: "productions if_table 2 = Some if_p2"
  by (simp add: if_table_def if_productions_def)

lemma if_productions_3 [simp]: "productions if_table 3 = Some if_p3"
  by (simp add: if_table_def if_productions_def)

lemma if_productions_4 [simp]: "productions if_table 4 = Some if_p4"
  by (simp add: if_table_def if_productions_def)

lemma if_reduce_actions:
  "actions if_table s tok = Some (ActReduce rid) \<Longrightarrow>
   (s = 2 \<and> rid = 1) \<or> (s = 7 \<and> rid = 3) \<or>
   (s = 8 \<and> rid = 4) \<or> (s = 9 \<and> rid = 2)"
  unfolding if_table_def if_actions_def
  by (auto split: if_splits prod.splits)

lemma if_goto_start:
  "gotos if_table s' ''Start'' = Some g \<Longrightarrow> g = 1"
  unfolding if_table_def if_gotos_def
  by (auto split: if_splits prod.splits)

lemma if_goto_ifblock:
  "gotos if_table s' ''IfBlock'' = Some g \<Longrightarrow> g = 2 \<or> g = 7"
  unfolding if_table_def if_gotos_def
  by (auto split: if_splits prod.splits)

lemma if_goto_else:
  "gotos if_table s' ''ElseClause'' = Some g \<Longrightarrow> g = 9"
  unfolding if_table_def if_gotos_def
  by (auto split: if_splits prod.splits)

lemma if_no_shift_end:
  "actions if_table s end_token = Some (ActShift st) \<Longrightarrow> False"
  unfolding if_table_def if_actions_def
  by (auto split: if_splits prod.splits)


text \<open>
  Coverage of the reduce graph: the four reduce actions of the table map to
  exactly the five edges of @{text if_reduce_edges}.  The proof classifies the
  action of a reduce step, and then reads off the goto entry of the reduced
  production; it never enumerates the parse tables with @{text auto}.
\<close>

lemma if_reduce_graph_pair:
  "(s, g) \<in> reduce_graph if_table \<Longrightarrow> (s, g) \<in> if_reduce_edges"
proof -
  assume mem: "(s, g) \<in> reduce_graph if_table"
  from mem obtain tok rid p s' where
    dec: "s \<in> states if_table \<and>
      actions if_table s tok = Some (ActReduce rid) \<and>
      productions if_table rid = Some p \<and>
      s' \<in> states if_table \<and>
      gotos if_table s' (lhs p) = Some g \<and>
      g \<in> states if_table"
    unfolding reduce_graph_def by blast
  from dec have act: "actions if_table s tok = Some (ActReduce rid)"
    and prod: "productions if_table rid = Some p"
    and goto: "gotos if_table s' (lhs p) = Some g"
    by blast+
  from if_reduce_actions[OF act]
  consider (r_one) "s = 2" "rid = 1"
    | (r_two) "s = 7" "rid = 3"
    | (r_three) "s = 8" "rid = 4"
    | (r_four) "s = 9" "rid = 2"
    by blast
  then show "(s, g) \<in> if_reduce_edges"
  proof cases
    case r_one
    have s_eq: "s = 2" using r_one by simp
    have rid_eq: "rid = 1" using r_one by simp
    have p_eq: "p = if_p1" using prod rid_eq if_productions_1
      by (metis option.inject)
    have goto': "gotos if_table s' ''Start'' = Some g"
      using goto p_eq by simp
    have g_eq: "g = 1" by (rule if_goto_start[OF goto'])
    show ?thesis using s_eq g_eq by (simp add: if_reduce_edges_def)
  next
    case r_two
    have s_eq: "s = 7" using r_two by simp
    have rid_eq: "rid = 3" using r_two by simp
    have p_eq: "p = if_p3" using prod rid_eq if_productions_3
      by (metis option.inject)
    have goto': "gotos if_table s' ''ElseClause'' = Some g"
      using goto p_eq by simp
    have g_eq: "g = 9" by (rule if_goto_else[OF goto'])
    show ?thesis using s_eq g_eq by (simp add: if_reduce_edges_def)
  next
    case r_three
    have s_eq: "s = 8" using r_three by simp
    have rid_eq: "rid = 4" using r_three by simp
    have p_eq: "p = if_p4" using prod rid_eq if_productions_4
      by (metis option.inject)
    have goto': "gotos if_table s' ''ElseClause'' = Some g"
      using goto p_eq by simp
    have g_eq: "g = 9" by (rule if_goto_else[OF goto'])
    show ?thesis using s_eq g_eq by (simp add: if_reduce_edges_def)
  next
    case r_four
    have s_eq: "s = 9" using r_four by simp
    have rid_eq: "rid = 2" using r_four by simp
    have p_eq: "p = if_p2" using prod rid_eq if_productions_2
      by (metis option.inject)
    have goto': "gotos if_table s' ''IfBlock'' = Some g"
      using goto p_eq by simp
    have g_cases: "g = 2 \<or> g = 7" by (rule if_goto_ifblock[OF goto'])
    from g_cases show ?thesis
    proof
      assume "g = 2"
      with s_eq show ?thesis by (simp add: if_reduce_edges_def)
    next
      assume "g = 7"
      with s_eq show ?thesis by (simp add: if_reduce_edges_def)
    qed
  qed
qed

lemma if_reduce_graph_subset:
  "reduce_graph if_table \<subseteq> if_reduce_edges"
proof (rule subsetI)
  fix x
  assume x: "x \<in> reduce_graph if_table"
  have pair: "(fst x, snd x) \<in> reduce_graph if_table" using x by simp
  have "(fst x, snd x) \<in> if_reduce_edges"
    by (rule if_reduce_graph_pair[OF pair])
  then show "x \<in> if_reduce_edges" by simp
qed

lemma if_edges_set_eq:
  "set if_reduce_edge_list = if_reduce_edges"
  by (simp add: if_reduce_edge_list_def if_reduce_edges_def)
lemma if_generated_rank_check_fails:
  "\<not> reduce_rank_check if_reduce_edge_list
    (auto_reduce_rank if_reduce_edge_list)"
  by eval

text \<open>
  The cycle of the reduce graph is witnessed by the reduction of
  @{text if_p3} at state 7 (which returns to state 9) and the reduction of
  @{text if_p2} at state 9 (which returns to state 7).
\<close>

lemma if_reduce_cycle_edges:
  "(7, 9) \<in> reduce_graph if_table"
  "(9, 7) \<in> reduce_graph if_table"
proof -
  have st_7: "7 \<in> states if_table" by (simp add: if_table_def)
  have st_9: "9 \<in> states if_table" by (simp add: if_table_def)
  have st_5: "5 \<in> states if_table" by (simp add: if_table_def)
  have st_6: "6 \<in> states if_table" by (simp add: if_table_def)
  have act_7: "actions if_table 7 end_token = Some (ActReduce 3)"
    by (simp add: if_table_def if_actions_def)
  have act_9: "actions if_table 9 end_token = Some (ActReduce 2)"
    by (simp add: if_table_def if_actions_def)
  have goto_5: "gotos if_table 5 (lhs if_p3) = Some 9"
    by (simp add: if_table_def if_gotos_def if_p3_def)
  have goto_6: "gotos if_table 6 (lhs if_p2) = Some 7"
    by (simp add: if_table_def if_gotos_def if_p2_def)
  have ex_7_9: "\<exists>tok rid p s'.
      actions if_table 7 tok = Some (ActReduce rid) \<and>
      productions if_table rid = Some p \<and>
      s' \<in> states if_table \<and>
      gotos if_table s' (lhs p) = Some 9"
    by (metis act_7 goto_5 if_productions_3 st_5)
  have ex_9_7: "\<exists>tok rid p s'.
      actions if_table 9 tok = Some (ActReduce rid) \<and>
      productions if_table rid = Some p \<and>
      s' \<in> states if_table \<and>
      gotos if_table s' (lhs p) = Some 7"
    by (metis act_9 goto_6 if_productions_2 st_6)
  from st_7 ex_7_9 st_9 show "(7, 9) \<in> reduce_graph if_table"
    unfolding reduce_graph_def by simp
  from st_9 ex_9_7 st_7 show "(9, 7) \<in> reduce_graph if_table"
    unfolding reduce_graph_def by simp
qed

lemma if_reduce_graph_not_acyclic:
  "\<not> acyclic (reduce_graph if_table)"
proof
  assume "acyclic (reduce_graph if_table)"
  then have "\<forall>s. (s, s) \<notin> (reduce_graph if_table)\<^sup>+"
    unfolding acyclic_def .
  moreover have "(7, 7) \<in> (reduce_graph if_table)\<^sup>+"
    using if_reduce_cycle_edges by (meson trancl.intros)
  ultimately show False by blast
qed
lemma if_no_state_reduce_rank:
  "\<not> (\<exists>rank :: state \<Rightarrow> nat.
      reduce_state_rank_certificate if_table rank)"
proof
  assume "\<exists>rank :: state \<Rightarrow> nat.
      reduce_state_rank_certificate if_table rank"
  then obtain rank :: "state \<Rightarrow> nat" where
      rank_certificate: "reduce_state_rank_certificate if_table rank"
    by blast
  have rank_7_9: "rank 9 < rank 7"
    using reduce_graph_rank_decreases[OF rank_certificate]
      if_reduce_cycle_edges(1) by blast
  have rank_9_7: "rank 7 < rank 9"
    using reduce_graph_rank_decreases[OF rank_certificate]
      if_reduce_cycle_edges(2) by blast
  from rank_7_9 rank_9_7 show False by simp
qed
text \<open>
  The height-based measure.  The table-specific content is captured by
  @{term "height_reduce_ok"}: every reduce either pops at least two symbols,
  or pops exactly one and strictly lowers an integer weight of the state it
  exposes.  Here the weight is @{text 1} on state @{text 2} and @{text 0}
  elsewhere: the only one-symbol reduce (state 2, production 1) exposes state
  1, so it lowers the weight, while the three multi-symbol reduces shrink the
  stack on their own.
\<close>

definition if_height :: "state \<Rightarrow> nat" where
  "if_height s = (if s = 2 then 1 else 0)"

lemma if_height_bound: "if_height s < 2"
  by (simp add: if_height_def)

lemma if_end_shift_free: "end_shift_free if_table"
  unfolding end_shift_free_def
  by (auto dest: if_no_shift_end)

lemma if_height_reduce_ok: "height_reduce_ok if_table if_height"
  unfolding height_reduce_ok_def
proof (intro allI impI)
  fix s tok rid p s' g
  assume act: "actions if_table s tok = Some (ActReduce rid)"
    and prod: "productions if_table rid = Some p"
    and goto: "gotos if_table s' (lhs p) = Some g"
  from if_reduce_actions[OF act]
  consider (one) "s = 2" "rid = 1" | (three) "s = 7" "rid = 3"
    | (four) "s = 8" "rid = 4" | (two) "s = 9" "rid = 2"
    by blast
  then show "2 \<le> length (rhs p) \<or>
      (length (rhs p) = 1 \<and> if_height g < if_height s)"
  proof cases
    case one
    have rid_one: "rid = 1" using one by simp
    have prod_one: "productions if_table 1 = Some if_p1" by (rule if_productions_1)
    with prod rid_one have p_eq: "p = if_p1" by (metis option.inject)
    have lhs_eq: "lhs p = ''Start''" using p_eq by simp
    have goto_start: "gotos if_table s' ''Start'' = Some g"
      using goto lhs_eq by simp
    have g_eq: "g = 1" by (rule if_goto_start[OF goto_start])
    have h_eq: "if_height g < if_height s"
      using one g_eq unfolding if_height_def by simp
    have len_one: "length (rhs p) = 1" using p_eq by simp
    show ?thesis by (rule disjI2, intro conjI, rule len_one, rule h_eq)
  next
    case three
    have rid_three: "rid = 3" using three by simp
    have prod_three: "productions if_table 3 = Some if_p3" by (rule if_productions_3)
    with prod rid_three have p_eq: "p = if_p3" by (metis option.inject)
    have "2 \<le> length (rhs p)" using p_eq by simp
    then show ?thesis by (rule disjI1)
  next
    case four
    have rid_four: "rid = 4" using four by simp
    have prod_four: "productions if_table 4 = Some if_p4" by (rule if_productions_4)
    with prod rid_four have p_eq: "p = if_p4" by (metis option.inject)
    have "2 \<le> length (rhs p)" using p_eq by simp
    then show ?thesis by (rule disjI1)
  next
    case two
    have rid_two: "rid = 2" using two by simp
    have prod_two: "productions if_table 2 = Some if_p2" by (rule if_productions_2)
    with prod rid_two have p_eq: "p = if_p2" by (metis option.inject)
    have "2 \<le> length (rhs p)" using p_eq by simp
    then show ?thesis by (rule disjI1)
  qed
qed

text \<open>
  What the executable rank generator returns on this table.  The value is
  finite and stable, but the generated rank is not a rank certificate: the
  reduce graph has a cycle, so no state-only rank can decrease along it.
\<close>

lemma if_generated_rank_2: "if_auto_reduce_rank 2 = 2"
  by eval

lemma if_generated_rank_7: "if_auto_reduce_rank 7 = 6"
  by eval

lemma if_generated_rank_8: "if_auto_reduce_rank 8 = 6"
  by eval

lemma if_generated_rank_9: "if_auto_reduce_rank 9 = 6"
  by eval

text \<open>
  The unified certificate.  Compared with the ad-hoc proof of the previous
  version, all reduction-step analysis is now inside the generic lemma
  @{thm [source] termination_certificate_height}; the table contributes only
  @{thm [source] if_end_shift_free} and @{thm [source] if_height_reduce_ok}.
\<close>

lemma if_termination_certificate:
  "termination_certificate if_table toks"
  by (rule termination_certificate_height
      [OF if_end_shift_free if_height_reduce_ok if_height_bound])

theorem if_lalr_termination:
  "finite_execution_target if_table toks"
  by (rule termination_certificate_finite_execution
      [OF if_termination_certificate])

corollary if_lalr_terminates:
  "\<exists>n r. run_rel if_table (init_config if_table toks) r n"
  using if_lalr_termination unfolding finite_execution_target_def .

end
