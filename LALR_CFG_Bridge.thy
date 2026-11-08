theory LALR_CFG_Bridge
  imports LALR_Recognizer
begin

definition production_rule :: "production \<Rightarrow> symbol rule" where
  "production_rule p = (lhs p, rhs p)"

definition table_productions :: "lalr_table \<Rightarrow> production set" where
  "table_productions t = {p. \<exists>rid. productions t rid = Some p}"

definition ordinary_input :: "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "ordinary_input t toks \<longleftrightarrow> set toks \<subseteq> terminals t - {end_token}"

definition table_represents_cfg :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "table_represents_cfg G t \<longleftrightarrow>
    (\<forall>rid p. productions t rid = Some p \<longrightarrow> number p = rid) \<and>
    (\<exists>aug_id aug.
      productions t aug_id = Some aug \<and>
      rhs aug = [Nonterminal (\<SS> G)] \<and>
      (\<forall>rid p. productions t rid = Some p \<and> rid \<noteq> aug_id \<longrightarrow>
        production_rule p \<in> set (\<RR> G)) \<and>
      (\<forall>r \<in> set (\<RR> G). \<exists>rid p.
        productions t rid = Some p \<and> production_rule p = r))"

definition table_compatible :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "table_compatible G t \<longleftrightarrow> wf_table t \<and> table_represents_cfg G t"

definition production_symbols_wf :: "lalr_table \<Rightarrow> production \<Rightarrow> bool" where
  "production_symbols_wf t p \<longleftrightarrow>
    lhs p \<in> nonterminals t \<and>
    (\<forall>x \<in> set (rhs p).
      case x of
        Terminal tok \<Rightarrow> tok \<in> terminals t - {end_token}
      | Nonterminal nt \<Rightarrow> nt \<in> nonterminals t)"

definition action_entries_wf :: "lalr_table \<Rightarrow> bool" where
  "action_entries_wf t \<longleftrightarrow>
    (\<forall>s tok a. actions t s tok = Some a \<longrightarrow>
      s \<in> states t \<and> tok \<in> terminals t \<and>
      (a = ActAccept \<longrightarrow> tok = end_token) \<and>
      (tok = end_token \<longrightarrow> (\<forall>q. a \<noteq> ActShift q)))"

definition goto_entries_wf :: "lalr_table \<Rightarrow> bool" where
  "goto_entries_wf t \<longleftrightarrow>
    (\<forall>s nt q. gotos t s nt = Some q \<longrightarrow>
      s \<in> states t \<and> nt \<in> nonterminals t \<and> q \<in> states t)"

definition augmented_start_wf :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "augmented_start_wf G t \<longleftrightarrow>
    (\<exists>rid p. productions t rid = Some p \<and>
      lhs p \<notin> set (map fst (\<RR> G)) \<union> {\<SS> G} \<and>
      rhs p = [Nonterminal (\<SS> G)])"

definition lalr_table_certificate :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "lalr_table_certificate G t \<longleftrightarrow>
    table_compatible G t \<and>
    terminals t \<inter> nonterminals t = {} \<and>
    end_token \<in> terminals t \<and>
    action_entries_wf t \<and>
    goto_entries_wf t \<and>
    augmented_start_wf G t \<and>
    (\<forall>rid p. productions t rid = Some p \<longrightarrow>
      production_symbols_wf t p)"

definition accepts :: "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "accepts t toks \<longleftrightarrow>
    (\<exists>n tr. run_rel t (init_config t toks) (Accepted tr) n)"

lemma table_production_member:
  "productions t rid = Some p \<Longrightarrow> p \<in> table_productions t"
  by (auto simp: table_productions_def)

lemma accepts_iff_recognize_detailed:
  "accepts t toks \<longleftrightarrow>
    (\<exists>fuel tr. recognize_detailed fuel t toks = Some (Accepted tr))"
  unfolding accepts_def recognize_detailed_def
  by (auto simp: run_detailed_fuel_iff_run_rel)

lemma ordinary_input_no_end:
  "ordinary_input t toks \<Longrightarrow> end_token \<notin> set toks"
  by (auto simp: ordinary_input_def)

lemma lalr_table_certificate_compatible:
  "lalr_table_certificate G t \<Longrightarrow> table_compatible G t"
  by (simp add: lalr_table_certificate_def)

lemma lalr_table_certificate_action_entries:
  "lalr_table_certificate G t \<Longrightarrow> action_entries_wf t"
  by (simp add: lalr_table_certificate_def)

lemma lalr_table_certificate_goto_entries:
  "lalr_table_certificate G t \<Longrightarrow> goto_entries_wf t"
  by (simp add: lalr_table_certificate_def)

end