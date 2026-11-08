theory LALR_Generator
  imports LALR_Soundness LALR_Termination_Schema
begin

text \<open>
  The generator interface.

  Up to now every table is verified by hand: we exhibit the item map, check the
  item certificate, and check the reduction rank.  This theory collects those
  per-table obligations into two predicates, @{text lalr_parser_certificate} and
  @{text lalr_termination_certificate}, and states the interface a table
  generator has to deliver.  Once a generator is implemented it only has to
  prove these two facts, once and for all grammars; every concrete table then
  follows by instantiation (see the locale @{text lalr_generator} below).

  @{text lalr_grammar} is deliberately left uninterpreted here: its definition
  (FIRST/FOLLOW based conflict freeness and action totality) belongs to the
  completeness development, where it is actually used.  Soundness, as
  established in @{text LALR_Soundness}, never needs it.
\<close>

consts lalr_grammar :: "symbol cfg \<Rightarrow> bool"

text \<open>
  The one obligation of the table that cannot be read off the item certificate:
  an accepting configuration has stacked exactly the start state and the one
  state reached by the goto on the start symbol.  For a concrete table this is
  discharged by the state height invariant (states \<open>0\<close> and \<open>1\<close> only), not by
  the full uniqueness assumptions of the plan.
\<close>

definition accept_shape_ok :: "lalr_table \<Rightarrow> token list \<Rightarrow> bool" where
  "accept_shape_ok t toks \<longleftrightarrow>
     (\<forall>cfg tr. reachable_cfg t toks cfg \<longrightarrow> one_step t cfg = Done (Accepted tr) \<longrightarrow>
        length (state_stack cfg) = 2)"

definition lalr_parser_certificate :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> bool" where
  "lalr_parser_certificate G t \<longleftrightarrow>
     wf_table t \<and>
     (\<exists>items bound initial_items lookaheads.
        lalr_sound_certificate G t items bound initial_items lookaheads \<and>
        (\<forall>item \<in> initial_items. snd item = 0)) \<and>
     (\<forall>toks. ordinary_input t toks \<longrightarrow> accept_shape_ok t toks)"

lemma lalr_parser_certificate_wf:
  "lalr_parser_certificate G t \<Longrightarrow> wf_table t"
  unfolding lalr_parser_certificate_def by blast

lemma lalr_parser_certificate_sound:
  "lalr_parser_certificate G t \<Longrightarrow>
   \<exists>items bound initial_items lookaheads.
      lalr_sound_certificate G t items bound initial_items lookaheads \<and>
      (\<forall>item \<in> initial_items. snd item = 0)"
  unfolding lalr_parser_certificate_def by blast

lemma lalr_parser_certificate_accept_shape:
  "lalr_parser_certificate G t \<Longrightarrow> ordinary_input t toks \<Longrightarrow> accept_shape_ok t toks"
  unfolding lalr_parser_certificate_def by blast

text \<open>
  The language direction of the interface: a table that carries a parser
  certificate accepts only words of the grammar.
\<close>

theorem lalr_accepts_sound:
  assumes cert: "lalr_parser_certificate G t"
    and ordinary: "ordinary_input t toks"
    and accepts: "accepts t toks"
  shows "toks \<in> language G"
proof -
  from cert obtain items bound initial_items lookaheads where
    sound: "lalr_sound_certificate G t items bound initial_items lookaheads"
    and zero: "\<forall>item \<in> initial_items. snd item = 0"
    using lalr_parser_certificate_sound [OF cert] by blast
  have shape_ok: "accept_shape_ok t toks"
    using cert ordinary by (rule lalr_parser_certificate_accept_shape)
  have shape: "\<And>cfg tr. reachable_cfg t toks cfg \<Longrightarrow>
        one_step t cfg = Done (Accepted tr) \<Longrightarrow> length (state_stack cfg) = 2"
    using shape_ok unfolding accept_shape_ok_def by blast
  show ?thesis by (rule accepts_sound [OF sound zero shape ordinary accepts])
qed

text \<open>
  The termination side of the interface, in the height form of
  @{text LALR_Termination_Schema}: a bound on the per-state height and the
  observation that every reduction of length \<open>\<ge> 2\<close> drops the stack.
\<close>

definition lalr_termination_certificate :: "lalr_table \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "lalr_termination_certificate t h B \<longleftrightarrow>
     wf_table t \<and> end_shift_free t \<and> height_reduce_ok t h \<and> (\<forall>s. h s < B)"

theorem lalr_termination_certificate_terminates:
  assumes cert: "lalr_termination_certificate t h B"
  shows "termination_certificate t toks"
proof -
  have parts: "wf_table t \<and> end_shift_free t \<and> height_reduce_ok t h \<and> (\<forall>s. h s < B)"
    using cert unfolding lalr_termination_certificate_def by blast
  from parts have free: "end_shift_free t" and ok: "height_reduce_ok t h"
    and bound: "\<forall>s. h s < B" by blast+
  show ?thesis
    by (rule termination_certificate_height [where B = B, OF free ok], simp add: bound)
qed

text \<open>
  A complete model certificate: one predicate that yields both the language
  theorem and termination for every input.
\<close>

definition lalr_model_certificate :: "symbol cfg \<Rightarrow> lalr_table \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "lalr_model_certificate G t h B \<longleftrightarrow>
     lalr_parser_certificate G t \<and> lalr_termination_certificate t h B"

theorem lalr_model_accepts_sound:
  assumes cert: "lalr_model_certificate G t h B"
    and ordinary: "ordinary_input t toks"
    and accepts: "accepts t toks"
  shows "toks \<in> language G"
proof -
  from cert have parser: "lalr_parser_certificate G t"
    unfolding lalr_model_certificate_def by blast
  show ?thesis by (rule lalr_accepts_sound [OF parser ordinary accepts])
qed

theorem lalr_model_terminates:
  assumes cert: "lalr_model_certificate G t h B"
  shows "termination_certificate t toks"
proof -
  from cert have termi: "lalr_termination_certificate t h B"
    unfolding lalr_model_certificate_def by blast
  show ?thesis by (rule lalr_termination_certificate_terminates [OF termi])
qed

text \<open>
  The generator contract.  A generator for LALR grammars must deliver, for
  every grammar that is LALR, a table together with a parser certificate and a
  termination certificate.  Everything else is proved once, here.
\<close>

locale lalr_generator =
  fixes generate :: "symbol cfg \<Rightarrow> lalr_table"
  assumes generate_parser_certificate:
    "lalr_grammar G \<Longrightarrow> lalr_parser_certificate G (generate G)"
  assumes generate_termination:
    "lalr_grammar G \<Longrightarrow> \<exists>h B. lalr_termination_certificate (generate G) h B"
begin

theorem generated_accepts_sound:
  assumes grammar: "lalr_grammar G"
    and ordinary: "ordinary_input (generate G) toks"
    and accepts: "accepts (generate G) toks"
  shows "toks \<in> language G"
proof -
  have parser: "lalr_parser_certificate G (generate G)"
    by (rule generate_parser_certificate [OF grammar])
  show ?thesis by (rule lalr_accepts_sound [OF parser ordinary accepts])
qed

theorem generated_terminates:
  assumes grammar: "lalr_grammar G"
  shows "termination_certificate (generate G) toks"
proof -
  obtain h where h_bound: "\<exists>B. lalr_termination_certificate (generate G) h B"
    by (rule exE [OF generate_termination [OF grammar]])
  obtain B where termi: "lalr_termination_certificate (generate G) h B"
    by (rule exE [OF h_bound])
  show ?thesis by (rule lalr_termination_certificate_terminates [OF termi])
qed

theorem generated_finite_execution:
  assumes grammar: "lalr_grammar G"
  shows "finite_execution_target (generate G) toks"
proof -
  have termi: "termination_certificate (generate G) toks"
    by (rule generated_terminates [OF grammar])
  show ?thesis by (rule termination_certificate_finite_execution [OF termi])
qed

end

text \<open>
  What remains for a concrete table after this interface: proving
  @{text lalr_parser_certificate} (item map, action correctness, the two
  explicit obligations) and @{text lalr_termination_certificate} (height and
  bound).  For the arithmetic table both are in reach: the item sets are the
  ten LR(0) closures of \<open>LALR_Items_Test\<close>, and the height is the
  @{text if_height}-style indicator used in the other case studies.
\<close>

end
