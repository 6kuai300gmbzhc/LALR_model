theory LALR_Properties
  imports LALR_Recognizer
begin

lemma init_stack_nonempty:
  "state_stack (init_config t toks) \<noteq> []"
  by (simp add: init_config_def)

lemma init_position_zero:
  "position (init_config t toks) = 0"
  by (simp add: init_config_def)

lemma init_input_has_end_token:
  "input_tokens (init_config t toks) = toks @ [end_token]"
  by (simp add: init_config_def)

lemma pop_rhs_none_iff:
  "pop_rhs n stk = None \<longleftrightarrow> length stk \<le> n"
  by (simp add: pop_rhs_def)

lemma pop_rhs_some_length:
  assumes "pop_rhs n stk = Some stk'"
  shows "length stk' = length stk - n"
  using assms
  by (metis append_eq_conv_conj append_take_drop_id diff_diff_cancel length_drop
      nat_le_linear option.distinct(1) option.inject pop_rhs_def take_all_iff)
end
