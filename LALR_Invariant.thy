theory LALR_Invariant
  imports LALR_CFG_Bridge
begin

definition consumed_tokens :: "config \<Rightarrow> token list" where
  "consumed_tokens cfg = take (position cfg) (input_tokens cfg)"

definition remaining_tokens :: "config \<Rightarrow> token list" where
  "remaining_tokens cfg = drop (position cfg) (input_tokens cfg)"

definition input_invariant :: "token list \<Rightarrow> config \<Rightarrow> bool" where
  "input_invariant toks cfg \<longleftrightarrow>
    input_tokens cfg = toks @ [end_token] \<and> position cfg \<le> length toks"

lemma input_invariant_init:
  "input_invariant toks (init_config t toks)"
  by (simp add: input_invariant_def init_config_def)

lemma consumed_tokens_init:
  "consumed_tokens (init_config t toks) = []"
  by (simp add: consumed_tokens_def init_config_def)

lemma remaining_tokens_init:
  "remaining_tokens (init_config t toks) = toks @ [end_token]"
  by (simp add: remaining_tokens_def init_config_def)

lemma input_invariant_consumed:
  assumes "input_invariant toks cfg"
  shows "consumed_tokens cfg = take (position cfg) toks"
  using assms
  by (simp add: consumed_tokens_def input_invariant_def)

lemma input_invariant_remaining:
  assumes "input_invariant toks cfg"
  shows "remaining_tokens cfg = drop (position cfg) toks @ [end_token]"
  using assms
  by (simp add: remaining_tokens_def input_invariant_def)

lemma step_next_input_frame:
  assumes "step t cfg (Next cfg')"
  shows "input_tokens cfg' = input_tokens cfg \<and>
    (position cfg' = position cfg \<or> position cfg' = Suc (position cfg))"
  using assms
  by (cases rule: step.cases) (auto simp: append_trace_def)

lemma shift_config_next_input_frame:
  assumes "append_trace
   (cfg\<lparr>state_stack := state_stack cfg @ [st], position := Suc (position cfg)\<rparr>) s la
   lbl =  cfg'"
  shows "input_tokens cfg' = input_tokens cfg \<and>
    position cfg' = Suc (position cfg)"
  using assms
  by (auto simp: append_trace_def)

lemma reduce_config_next_input_frame:
  assumes "append_trace (cfg\<lparr>state_stack := stk' @ [g]\<rparr>) s la lbl = cfg'"
  shows "input_tokens cfg' = input_tokens cfg \<and>
    position cfg' = position cfg"
  using assms
  by (auto simp: append_trace_def)

lemma one_step_next_input_frame:
  assumes "one_step t cfg = Next cfg'"
  shows "input_tokens cfg' = input_tokens cfg \<and>
    (position cfg' = position cfg \<or> position cfg' = Suc (position cfg))"
  using assms
  unfolding one_step_def
  apply (split if_splits)
   apply simp
  apply (split option.splits)
   apply simp
  apply (simp only: Let_def)
  apply (split option.splits)
   apply simp
  apply (split action.splits)
  subgoal
    by (auto simp: append_trace_def intro: shift_config_next_input_frame)
  subgoal for x2 x2a x2b
    by (auto simp: append_trace_def
        split: option.splits intro: reduce_config_next_input_frame)
  subgoal
    by simp
  done

end