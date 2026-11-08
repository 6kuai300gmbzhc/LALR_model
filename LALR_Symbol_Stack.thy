theory LALR_Symbol_Stack
  imports LALR_Termination_Schema
begin

text \<open>
  The recognizer keeps only a stack of states (see the @{typ config} record).
  For language level reasoning we need the corresponding stack of grammar
  symbols.  It is not stored in the configuration, so it is reconstructed from
  the run: a shift appends the consumed terminal, a reduction removes
  @{text "length (rhs p)"} symbols and appends the left hand side of the
  reduced production.

  The reduction case deliberately truncates with @{term take} instead of
  assuming that the removed symbols are exactly @{term "rhs p"}; the latter is
  the content of the soundness lemma @{text reduce_rhs_match} and is derived
  from the item invariants.

  On top of the symbol stack this theory defines the yield relation
  @{text parses} (the symbols spell out a terminal word, one production at a
  time) and the item tracking predicate @{text stack_tracks} (the state at
  every stack position is consistent with the symbols below it).
\<close>

section \<open>Symbol stacks reconstructed from executions\<close>

inductive stack_symbols ::
  "lalr_table \<Rightarrow> token list \<Rightarrow> config \<Rightarrow>
   symbol grammar_symbol list \<Rightarrow> bool"
where
  symbols_init:
    "stack_symbols t toks (init_config t toks) []"
| symbols_shift:
    "stack_symbols t toks cfg \<sigma> \<Longrightarrow>
     top_state (state_stack cfg) = Some s \<Longrightarrow>
     actions t s (input_tokens cfg ! position cfg) = Some (ActShift st) \<Longrightarrow>
     one_step t cfg = Next cfg' \<Longrightarrow>
     stack_symbols t toks cfg' (\<sigma> @ [Terminal (input_tokens cfg ! position cfg)])"
| symbols_reduce:
    "stack_symbols t toks cfg \<sigma> \<Longrightarrow>
     top_state (state_stack cfg) = Some s \<Longrightarrow>
     actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
     productions t rid = Some p \<Longrightarrow>
     one_step t cfg = Next cfg' \<Longrightarrow>
     stack_symbols t toks cfg'
       (take (length \<sigma> - length (rhs p)) \<sigma> @ [Nonterminal (lhs p)])"

lemma stack_symbols_init:
  "stack_symbols t toks (init_config t toks) []"
  by (rule symbols_init)

subsection \<open>Stack shape of a single step\<close>

lemma one_step_shift_stack:
  assumes "one_step t cfg = Next cfg'"
    and "top_state (state_stack cfg) = Some s"
    and "actions t s (input_tokens cfg ! position cfg) = Some (ActShift st)"
  shows "state_stack cfg' = state_stack cfg @ [st]"
  using assms
  unfolding one_step_def Let_def
  by (auto simp: append_trace_def split: option.splits action.splits if_splits)

lemma one_step_reduce_stack:
  assumes "one_step t cfg = Next cfg'"
    and "top_state (state_stack cfg) = Some s"
    and "actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid)"
    and "productions t rid = Some p"
  shows "\<exists>stk' g. pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<and>
                 state_stack cfg' = stk' @ [g]"
  using assms
  unfolding one_step_def Let_def
  by (auto simp: append_trace_def split: option.splits action.splits if_splits)

section \<open>The yield relation\<close>

inductive parses ::
  "symbol cfg \<Rightarrow> symbol grammar_symbol list \<Rightarrow>
   symbol grammar_symbol list \<Rightarrow> bool"
where
  parses_nil:
    "parses G [] []"
| parses_terminal:
    "parses G \<sigma> w \<Longrightarrow> parses G (Terminal a # \<sigma>) (Terminal a # w)"
| parses_nonterminal:
    "(A, \<alpha>) \<in> set (\<RR> G) \<Longrightarrow>
     parses G \<alpha> w1 \<Longrightarrow> parses G \<sigma> w \<Longrightarrow>
     parses G (Nonterminal A # \<sigma>) (w1 @ w)"

text \<open>
  @{text parses} is the ``these symbols produce this terminal word'' relation:
  a terminal produces itself, a nonterminal produces the yield of any of its
  right hand sides, and the yield of a sequence is the concatenation.  This is
  where the grammar enters the argument.
\<close>

lemma parses_nilD:
  assumes "parses G [] w"
  shows "w = []"
  by (rule parses.cases[OF assms]) auto

lemma parses_terminalD:
  assumes "parses G (Terminal a # \<sigma>) w"
  shows "\<exists>w'. w = Terminal a # w' \<and> parses G \<sigma> w'"
  by (rule parses.cases[OF assms]) auto

lemma parses_nonterminalD:
  assumes "parses G (Nonterminal A # \<sigma>) w"
  shows "\<exists>\<alpha> w1 w2. w = w1 @ w2 \<and> (A, \<alpha>) \<in> set (\<RR> G) \<and>
                   parses G \<alpha> w1 \<and> parses G \<sigma> w2"
  by (rule parses.cases[OF assms]) auto

subsection \<open>Derivations: congruence and composition\<close>

lemma derives_refl [simp]:
  "derives G u u"
  by (simp add: derives_def derivations_def)

lemma derives1_append:
  assumes "derives1 G u v"
  shows "derives1 G (x @ u @ y) (x @ v @ y)"
proof -
  from assms obtain u' v' A \<alpha> where dec:
    "u = u' @ [Nonterminal A] @ v'"
    "v = u' @ \<alpha> @ v'"
    "(A, \<alpha>) \<in> set (\<RR> G)"
    unfolding derives1_def by blast
  have lhs: "x @ u @ y = (x @ u') @ [Nonterminal A] @ (v' @ y)"
    using dec(1) by (simp add: append_assoc)
  have rhs: "x @ v @ y = (x @ u') @ \<alpha> @ (v' @ y)"
    using dec(2) by (simp add: append_assoc)
  show ?thesis
  proof (unfold derives1_def)
    show "\<exists>xa ya Aa \<alpha>a. x @ u @ y = xa @ [Nonterminal Aa] @ ya \<and>
              x @ v @ y = xa @ \<alpha>a @ ya \<and> (Aa, \<alpha>a) \<in> set (\<RR> G)"
      by (rule_tac x = "x @ u'" in exI, rule_tac x = "v' @ y" in exI,
          rule_tac x = A in exI, rule_tac x = \<alpha> in exI,
          intro conjI, rule lhs, rule rhs, rule dec(3))
  qed
qed

lemma derives1_member:
  "derives1 G u v \<Longrightarrow> (u, v) \<in> derivations1 G"
  unfolding derivations1_def by auto

lemma derives_append:
  assumes "derives G u v"
  shows "derives G (x @ u @ y) (x @ v @ y)"
proof -
  from assms have rel: "(u, v) \<in> (derivations1 G)\<^sup>*"
    unfolding derives_def derivations_def by simp
  have closed: "\<And>a b. (a, b) \<in> (derivations1 G)\<^sup>* \<Longrightarrow>
                       (x @ a @ y, x @ b @ y) \<in> (derivations1 G)\<^sup>*"
  proof -
    fix a b
    assume ab: "(a, b) \<in> (derivations1 G)\<^sup>*"
    from ab show "(x @ a @ y, x @ b @ y) \<in> (derivations1 G)\<^sup>*"
    proof (rule rtrancl_induct)
      show "(x @ a @ y, x @ a @ y) \<in> (derivations1 G)\<^sup>*" by simp
    next
      fix c d
      assume "(a, c) \<in> (derivations1 G)\<^sup>*"
        and cd: "(c, d) \<in> derivations1 G"
        and ih: "(x @ a @ y, x @ c @ y) \<in> (derivations1 G)\<^sup>*"
      have dc: "derives1 G c d" using cd by (auto simp: derivations1_def)
      have mapped: "derives1 G (x @ c @ y) (x @ d @ y)"
        by (rule derives1_append[OF dc])
      have s2: "(x @ c @ y, x @ d @ y) \<in> derivations1 G"
        by (rule derives1_member[OF mapped])
      from ih s2 show "(x @ a @ y, x @ d @ y) \<in> (derivations1 G)\<^sup>*"
        by (rule rtrancl_into_rtrancl)
    qed
  qed
  from closed[OF rel] show ?thesis
    unfolding derives_def derivations_def by simp
qed

lemma derives_trans:
  "derives G u v \<Longrightarrow> derives G v w \<Longrightarrow> derives G u w"
  unfolding derives_def derivations_def by (blast intro: rtrancl_trans)

lemma derives_step:
  "(A, \<alpha>) \<in> set (\<RR> G) \<Longrightarrow>
   derives G (x @ [Nonterminal A] @ y) (x @ \<alpha> @ y)"
proof -
  assume rule: "(A, \<alpha>) \<in> set (\<RR> G)"
  have d1: "derives1 G (x @ [Nonterminal A] @ y) (x @ \<alpha> @ y)"
  proof -
    have "x @ [Nonterminal A] @ y = x @ [Nonterminal A] @ y \<and>
          x @ \<alpha> @ y = x @ \<alpha> @ y \<and> (A, \<alpha>) \<in> set (\<RR> G)"
      using rule by simp
    then show ?thesis unfolding derives1_def by blast
  qed
  have m: "(x @ [Nonterminal A] @ y, x @ \<alpha> @ y) \<in> derivations1 G"
    using d1 by (rule derives1_member)
  show ?thesis unfolding derives_def derivations_def
    by (rule r_into_rtrancl[OF m])
qed

lemma derives_append_right:
  "derives G u v \<Longrightarrow> derives G (u @ suffix) (v @ suffix)"
  using derives_append[where x = "[]" and y = suffix] by simp

lemma derives_append_left:
  "derives G u v \<Longrightarrow> derives G (x @ u) (x @ v)"
  using derives_append[where y = "[]"] by simp

lemma derives_cons_terminal:
  "derives G \<sigma> w \<Longrightarrow> derives G (Terminal a # \<sigma>) (Terminal a # w)"
  using derives_append[where x = "[Terminal a]" and y = "[]"] by simp

lemma derives_cons_nonterminal:
  "(A, \<alpha>) \<in> set (\<RR> G) \<Longrightarrow>
   derives G (Nonterminal A # \<sigma>) (\<alpha> @ \<sigma>)"
  using derives_step[where x = "[]" and y = \<sigma>] by simp

lemma parses_derives:
  "parses G \<sigma> w \<Longrightarrow> derives G \<sigma> w"
proof -
  assume p: "parses G \<sigma> w"
  from p show "derives G \<sigma> w"
  proof (rule parses.induct)
    fix G
    show "derives G [] []" by simp
  next
    fix G \<sigma> w a
    assume ps: "parses G \<sigma> w" and ih: "derives G \<sigma> w"
    from ih show "derives G (Terminal a # \<sigma>) (Terminal a # w)"
      by (rule derives_cons_terminal)
  next
    fix A \<alpha> G w1 \<sigma> w
    assume rule: "(A, \<alpha>) \<in> set (\<RR> G)"
      and "parses G \<alpha> w1" and ih1: "derives G \<alpha> w1"
      and "parses G \<sigma> w" and ih2: "derives G \<sigma> w"
    have head: "derives G (Nonterminal A # \<sigma>) (\<alpha> @ \<sigma>)"
      by (rule derives_cons_nonterminal[OF rule])
    have mid: "derives G (\<alpha> @ \<sigma>) (w1 @ \<sigma>)"
      using derives_append[where G = G and u = \<alpha> and v = w1 and x = "[]" and y = \<sigma>, OF ih1]
      by simp
    have last: "derives G (w1 @ \<sigma>) (w1 @ w)"
      using derives_append[where G = G and u = \<sigma> and v = w and x = w1 and y = "[]", OF ih2]
      by simp
    have chain1: "derives G (Nonterminal A # \<sigma>) (w1 @ \<sigma>)"
      using head mid by (rule derives_trans)
    have chain2: "derives G (Nonterminal A # \<sigma>) (w1 @ w)"
      using chain1 last by (rule derives_trans)
    from chain2 show "derives G (Nonterminal A # \<sigma>) (w1 @ w)" .
  qed
qed

subsection \<open>Composition and splitting of yields\<close>

lemma parses_append:
  "parses G \<sigma> w \<Longrightarrow> parses G \<tau> u \<Longrightarrow> parses G (\<sigma> @ \<tau>) (w @ u)"
proof (induct \<sigma> arbitrary: w)
  case Nil
  from Nil.prems(1) have "w = []" by (rule parses_nilD)
  with Nil.prems(2) show ?case by simp
next
  case (Cons x \<sigma>)
  note prems = Cons.prems
  show ?case
  proof (cases x)
    case (Terminal a)
    have p: "parses G (Terminal a # \<sigma>) w" using prems(1) Terminal by simp
    have ex: "\<exists>w'. w = Terminal a # w' \<and> parses G \<sigma> w'"
      using p by (rule parses_terminalD)
    obtain w' where w_eq: "w = Terminal a # w'" and rest: "parses G \<sigma> w'"
      using ex by blast
    have ih: "parses G (\<sigma> @ \<tau>) (w' @ u)" using rest prems(2) by (rule Cons.hyps)
    have "parses G (Terminal a # (\<sigma> @ \<tau>)) (Terminal a # (w' @ u))"
      by (rule parses_terminal[OF ih])
    then show ?thesis using w_eq Terminal by simp
  next
    case (Nonterminal A)
    have p: "parses G (Nonterminal A # \<sigma>) w" using prems(1) Nonterminal by simp
    have ex: "\<exists>\<alpha> w1 w2. w = w1 @ w2 \<and> (A, \<alpha>) \<in> set (\<RR> G) \<and>
                             parses G \<alpha> w1 \<and> parses G \<sigma> w2"
      using p by (rule parses_nonterminalD)
    obtain \<alpha> w1 w2 where w_eq: "w = w1 @ w2"
      and rule: "(A, \<alpha>) \<in> set (\<RR> G)"
      and p1: "parses G \<alpha> w1" and p2: "parses G \<sigma> w2"
      using ex by blast
    have ih: "parses G (\<sigma> @ \<tau>) (w2 @ u)" using p2 prems(2) by (rule Cons.hyps)
    have "parses G (Nonterminal A # (\<sigma> @ \<tau>)) (w1 @ (w2 @ u))"
      using rule p1 ih by (rule parses_nonterminal)
    then show ?thesis using w_eq Nonterminal by (simp add: append_assoc)
  qed
qed

lemma parses_append_terminal:
  assumes "parses G \<sigma> w"
  shows "parses G (\<sigma> @ [Terminal a]) (w @ [Terminal a])"
proof -
  have one: "parses G [Terminal a] [Terminal a]"
    by (rule parses_terminal[OF parses_nil])
  show ?thesis using assms one by (rule parses_append)
qed

lemma parses_append_split:
  "parses G (\<sigma> @ \<tau>) w \<Longrightarrow>
   \<exists>w1 w2. w = w1 @ w2 \<and> parses G \<sigma> w1 \<and> parses G \<tau> w2"
proof (induct \<sigma> arbitrary: w)
  case Nil
  then show ?case by (auto intro: parses_nil)
next
  case (Cons x \<sigma>)
  note prems = Cons.prems
  show ?case
  proof (cases x)
    case (Terminal a)
    have p: "parses G (Terminal a # (\<sigma> @ \<tau>)) w" using prems Terminal by simp
    have ex: "\<exists>w'. w = Terminal a # w' \<and> parses G (\<sigma> @ \<tau>) w'"
      using p by (rule parses_terminalD)
    obtain w' where w_eq: "w = Terminal a # w'" and rest: "parses G (\<sigma> @ \<tau>) w'"
      using ex by blast
    have ex2: "\<exists>w1 w2. w' = w1 @ w2 \<and> parses G \<sigma> w1 \<and> parses G \<tau> w2"
      using rest by (rule Cons.hyps)
    obtain w1 w2 where w_eq': "w' = w1 @ w2"
      and p1: "parses G \<sigma> w1" and p2: "parses G \<tau> w2"
      using ex2 by blast
    have pt: "parses G (Terminal a # \<sigma>) (Terminal a # w1)"
      by (rule parses_terminal[OF p1])
    show ?thesis
    proof (rule_tac x = "Terminal a # w1" in exI, rule_tac x = w2 in exI, intro conjI)
      show "w = (Terminal a # w1) @ w2" using w_eq w_eq' by simp
      show "parses G (x # \<sigma>) (Terminal a # w1)" using pt Terminal by simp
      show "parses G \<tau> w2" by (rule p2)
    qed
  next
    case (Nonterminal A)
    have p: "parses G (Nonterminal A # (\<sigma> @ \<tau>)) w"
      using prems Nonterminal by simp
    have ex: "\<exists>\<alpha> w1 w2. w = w1 @ w2 \<and> (A, \<alpha>) \<in> set (\<RR> G) \<and>
                             parses G \<alpha> w1 \<and> parses G (\<sigma> @ \<tau>) w2"
      using p by (rule parses_nonterminalD)
    obtain \<alpha> w1 w2 where w_eq: "w = w1 @ w2"
      and rule: "(A, \<alpha>) \<in> set (\<RR> G)"
      and p1: "parses G \<alpha> w1" and p2: "parses G (\<sigma> @ \<tau>) w2"
      using ex by blast
    have ex2: "\<exists>u1 u2. w2 = u1 @ u2 \<and> parses G \<sigma> u1 \<and> parses G \<tau> u2"
      using p2 by (rule Cons.hyps)
    obtain u1 u2 where w2_eq: "w2 = u1 @ u2"
      and q1: "parses G \<sigma> u1" and q2: "parses G \<tau> u2"
      using ex2 by blast
    have pn: "parses G (Nonterminal A # \<sigma>) (w1 @ u1)"
      using rule p1 q1 by (rule parses_nonterminal)
    show ?thesis
    proof (rule_tac x = "w1 @ u1" in exI, rule_tac x = u2 in exI, intro conjI)
      show "w = (w1 @ u1) @ u2" using w_eq w2_eq by (simp add: append_assoc)
      show "parses G (x # \<sigma>) (w1 @ u1)" using pn Nonterminal by simp
      show "parses G \<tau> u2" by (rule q2)
    qed
  qed
qed

section \<open>Item tracking along the state stack\<close>

text \<open>
  A state tracks a symbol prefix if every item of the state is consistent with
  that prefix: the dot of the item is inside the prefix, and the symbols before
  the dot match the end of the prefix.  The predicate is applied to every
  stack position (with the prefix @{text "take j \<sigma>"}), not only to the top,
  because after a reduction the new top is a state that was previously deeper
  in the stack.
\<close>

definition tracks ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   symbol grammar_symbol list \<Rightarrow> state \<Rightarrow> bool" where
  "tracks t items \<sigma> s \<longleftrightarrow>
     (\<forall>item \<in> state_items items s.
        \<forall>p. productions t (fst item) = Some p \<longrightarrow>
          snd item \<le> length \<sigma> \<and>
          take (snd item) (rhs p) = drop (length \<sigma> - snd item) \<sigma>)"

definition stack_tracks ::
  "lalr_table \<Rightarrow> state_item_map \<Rightarrow>
   symbol grammar_symbol list \<Rightarrow> state list \<Rightarrow> bool" where
  "stack_tracks t items \<sigma> stk \<longleftrightarrow>
     length \<sigma> + 1 = length stk \<and>
     (\<forall>j < length stk. tracks t items (take j \<sigma>) (stk ! j))"

lemma stack_tracks_length:
  "stack_tracks t items \<sigma> stk \<Longrightarrow> length \<sigma> + 1 = length stk"
  by (simp add: stack_tracks_def)

lemma tracks_length_le:
  assumes "tracks t items \<sigma> s"
    and "item \<in> state_items items s"
    and "productions t (fst item) = Some p"
  shows "snd item \<le> length \<sigma>"
  using assms unfolding tracks_def by blast

lemma tracks_dot_match:
  assumes "tracks t items \<sigma> s"
    and "item \<in> state_items items s"
    and "productions t (fst item) = Some p"
  shows "take (snd item) (rhs p) = drop (length \<sigma> - snd item) \<sigma>"
  using assms unfolding tracks_def by blast

text \<open>
  The central consequence used in the soundness proof: a complete item at the
  top state forces the symbol stack to end with the right hand side.
\<close>

lemma tracks_complete_suffix:
  assumes "tracks t items \<sigma> s"
    and "item \<in> state_items items s"
    and "productions t (fst item) = Some p"
    and "snd item = length (rhs p)"
  shows "\<sigma> = take (length \<sigma> - length (rhs p)) \<sigma> @ rhs p"
proof -
  have len_le: "length (rhs p) \<le> length \<sigma>"
    using assms(1,2,3,4) by (metis tracks_length_le)
  have dot: "take (length (rhs p)) (rhs p) =
             drop (length \<sigma> - length (rhs p)) \<sigma>"
    using assms(1,2,3,4) by (metis tracks_dot_match)
  hence drop_eq: "drop (length \<sigma> - length (rhs p)) \<sigma> = rhs p" by simp
  have split: "take (length \<sigma> - length (rhs p)) \<sigma> @
               drop (length \<sigma> - length (rhs p)) \<sigma> = \<sigma>"
    by (rule append_take_drop_id)
  show ?thesis using split drop_eq by simp
qed

end
