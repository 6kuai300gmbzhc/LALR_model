theory LALR_Table
  imports CFG
begin

type_synonym symbol = string
type_synonym token = string
type_synonym nonterminal_ = string
type_synonym state = nat
type_synonym production_id = nat

abbreviation end_token :: token where
  "end_token \<equiv> ''END''"

record production =
  number :: production_id
  lhs :: nonterminal_
  rhs :: "symbol grammar_symbol list"

datatype action =
    ActShift state
  | ActReduce production_id
  | ActAccept

record lalr_table =
  parsing_method :: string
  terminals :: "token set"
  nonterminals :: "nonterminal_ set"
  states :: "state set"
  productions :: "production_id \<Rightarrow> production option"
  actions :: "state \<Rightarrow> token \<Rightarrow> action option"
  gotos :: "state \<Rightarrow> nonterminal_ \<Rightarrow> state option"
  start_state :: state

definition wf_table :: "lalr_table \<Rightarrow> bool" where
  "wf_table t \<longleftrightarrow>
    start_state t \<in> states t \<and>
    (\<forall>s tok st. actions t s tok = Some (ActShift st) \<longrightarrow> st \<in> states t) \<and>
    (\<forall>s tok rid. actions t s tok = Some (ActReduce rid) \<longrightarrow> productions t rid \<noteq> None) \<and>
    (\<forall>s nt st. gotos t s nt = Some st \<longrightarrow> st \<in> states t) \<and>
    (\<forall>s tok. tok \<noteq> end_token \<longrightarrow> actions t s tok \<noteq> Some ActAccept)"

end
