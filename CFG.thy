theory CFG
  imports Main
begin

datatype 'a grammar_symbol =
    Terminal 'a
  | Nonterminal 'a

type_synonym 'a rule = "'a \<times> 'a grammar_symbol list"

type_synonym 'a rules = "'a rule list"

datatype 'a cfg = CFG (\<RR> : "'a rules") (\<SS> : "'a")

definition nonterminals :: "'a cfg \<Rightarrow> 'a set" where
  "nonterminals G = set (map fst (\<RR> G)) \<union> {\<SS> G}"

definition is_word :: "'a cfg \<Rightarrow> 'a grammar_symbol list \<Rightarrow> bool" where
  "is_word \<G> \<omega> \<longleftrightarrow> (\<forall>x \<in> set \<omega>. \<exists>a. x = Terminal a)"

definition derives1 :: "'a cfg \<Rightarrow> 'a grammar_symbol list \<Rightarrow> 'a grammar_symbol list \<Rightarrow> bool" where
  "derives1 \<G> u v \<equiv> \<exists> x y A \<alpha>. 
    u = x @ [Nonterminal A] @ y \<and>
    v = x @ \<alpha> @ y \<and>
    (A, \<alpha>) \<in> set (\<RR> \<G>)"  

definition derivations1 :: "'a cfg \<Rightarrow> ('a grammar_symbol list \<times> 'a grammar_symbol list) set" where
  "derivations1 \<G> \<equiv> { (u,v) | u v. derives1 \<G> u v }"

definition derivations :: "'a cfg \<Rightarrow> ('a grammar_symbol list \<times> 'a grammar_symbol list) set" where 
  "derivations \<G> \<equiv> (derivations1 \<G>)^*"

definition derives :: "'a cfg \<Rightarrow> 'a grammar_symbol list \<Rightarrow> 'a grammar_symbol list \<Rightarrow> bool" where
  "derives \<G> u v \<equiv> ((u, v) \<in> derivations \<G>)"

definition language :: "'a cfg \<Rightarrow> 'a list set" where
  "language \<G> = {\<omega>. is_word \<G> (map Terminal \<omega>) \<and>
    derives \<G> [Nonterminal (\<SS> \<G>)] (map Terminal \<omega>)}"

lemma is_word_map_terminal [simp]:
  "is_word G (map Terminal \<omega>)"
  by (simp add: is_word_def)

lemma derives1_from_word_false:
  assumes "is_word G u"
  shows "\<not> derives1 G u v"
  using assms
  by (auto simp: derives1_def is_word_def)

end