theory LALR_Recognizer
  imports LALR_Table
begin

datatype step_label =
    StepShift state
  | StepReduce production_id
  | StepAccept

record trace_step =
  step_state :: state
  step_lookahead :: token
  step_action :: step_label

datatype error_kind =
    ErrNoAction state token
  | ErrUnknownProduction production_id
  | ErrStackUnderflow nat
  | ErrNoGoto state nonterminal_
  | ErrInputEndedWithoutAccept
  | ErrEmptyStateStack

record config =
  state_stack :: "state list"
  input_tokens :: "token list"
  position :: nat
  trace :: "trace_step list"

datatype run_result =
    Accepted "trace_step list"
  | Rejected error_kind "trace_step list"

datatype step_out =
    Next config
    | Done run_result



definition top_state :: "state list \<Rightarrow> state option" where
  "top_state stk = (if stk = [] then None else Some (last stk))"

definition append_trace :: "config \<Rightarrow> state \<Rightarrow> token \<Rightarrow> step_label \<Rightarrow> config" where
  "append_trace cfg s la lbl =
    cfg\<lparr>trace := trace cfg @ [\<lparr>step_state = s, step_lookahead = la, step_action = lbl\<rparr>]\<rparr>"

definition init_config :: "lalr_table \<Rightarrow> token list \<Rightarrow> config" where
  "init_config t toks =
    \<lparr>state_stack = [start_state t], input_tokens = toks @ [end_token], position = 0, trace = []\<rparr>"

definition pop_rhs :: "nat \<Rightarrow> state list \<Rightarrow> state list option" where
  "pop_rhs n stk = (if length stk \<le> n then None else Some (take (length stk - n) stk))"

inductive step :: "lalr_table \<Rightarrow> config \<Rightarrow> step_out \<Rightarrow> bool" where
  step_input_end:
    "position cfg \<ge> length (input_tokens cfg) \<Longrightarrow>
      step t cfg (Done (Rejected ErrInputEndedWithoutAccept (trace cfg)))"
| step_empty_stack:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      state_stack cfg = [] \<Longrightarrow>
      step t cfg (Done (Rejected ErrEmptyStateStack (trace cfg)))"
| step_no_action:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = None \<Longrightarrow>
      step t cfg (Done (Rejected (ErrNoAction s (input_tokens cfg ! position cfg)) (trace cfg)))"
| step_shift:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActShift st) \<Longrightarrow>
      step t cfg (Next (append_trace
        (cfg\<lparr>state_stack := state_stack cfg @ [st],
          position := position cfg + 1\<rparr>)
        s (input_tokens cfg ! position cfg) (StepShift st)))"
| step_unknown_production:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
      productions t rid = None \<Longrightarrow>
      step t cfg (Done (Rejected (ErrUnknownProduction rid) (trace cfg)))"
| step_stack_underflow:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
      productions t rid = Some p \<Longrightarrow>
      pop_rhs (length (rhs p)) (state_stack cfg) = None \<Longrightarrow>
      step t cfg (Done (Rejected (ErrStackUnderflow (length (rhs p))) (trace cfg)))"
| step_reduce_empty_stack:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
      productions t rid = Some p \<Longrightarrow>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<Longrightarrow>
      top_state stk' = None \<Longrightarrow>
      step t cfg (Done (Rejected ErrEmptyStateStack (trace cfg)))"
| step_no_goto:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
      productions t rid = Some p \<Longrightarrow>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<Longrightarrow>
      top_state stk' = Some s' \<Longrightarrow>
      gotos t s' (lhs p) = None \<Longrightarrow>
      step t cfg (Done (Rejected (ErrNoGoto s' (lhs p)) (trace cfg)))"
| step_reduce:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) \<Longrightarrow>
      productions t rid = Some p \<Longrightarrow>
      pop_rhs (length (rhs p)) (state_stack cfg) = Some stk' \<Longrightarrow>
      top_state stk' = Some s' \<Longrightarrow>
      gotos t s' (lhs p) = Some g \<Longrightarrow>
      step t cfg (Next (append_trace
        (cfg\<lparr>state_stack := stk' @ [g]\<rparr>)
        s (input_tokens cfg ! position cfg) (StepReduce (number p))))"
| step_accept:
    "position cfg < length (input_tokens cfg) \<Longrightarrow>
      top_state (state_stack cfg) = Some s \<Longrightarrow>
      actions t s (input_tokens cfg ! position cfg) = Some ActAccept \<Longrightarrow>
      step t cfg (Done (Accepted (trace (append_trace cfg s
        (input_tokens cfg ! position cfg) StepAccept))))"

definition one_step :: "lalr_table \<Rightarrow> config \<Rightarrow> step_out" where
  "one_step t cfg =
    (if position cfg \<ge> length (input_tokens cfg) then
       Done (Rejected ErrInputEndedWithoutAccept (trace cfg))
     else
       (case top_state (state_stack cfg) of
          None \<Rightarrow> Done (Rejected ErrEmptyStateStack (trace cfg))
        | Some s \<Rightarrow>
            let la = input_tokens cfg ! position cfg in
              (case actions t s la of
                 None \<Rightarrow> Done (Rejected (ErrNoAction s la) (trace cfg))
               | Some (ActShift st) \<Rightarrow>
                   let cfg1 = cfg\<lparr>state_stack := state_stack cfg @ [st], position := position cfg + 1\<rparr>;
                       cfg2 = append_trace cfg1 s la (StepShift st)
                   in Next cfg2
               | Some (ActReduce rid) \<Rightarrow>
                   (case productions t rid of
                      None \<Rightarrow> Done (Rejected (ErrUnknownProduction rid) (trace cfg))
                    | Some p \<Rightarrow>
                        (case pop_rhs (length (rhs p)) (state_stack cfg) of
                           None \<Rightarrow> Done (Rejected (ErrStackUnderflow (length (rhs p))) (trace cfg))
                         | Some stk' \<Rightarrow>
                             (case top_state stk' of
                                None \<Rightarrow> Done (Rejected ErrEmptyStateStack (trace cfg))
                              | Some s' \<Rightarrow>
                                  (case gotos t s' (lhs p) of
                                     None \<Rightarrow> Done (Rejected (ErrNoGoto s' (lhs p)) (trace cfg))
                                   | Some g \<Rightarrow>
                                       let cfg1 = cfg\<lparr>state_stack := stk' @ [g]\<rparr>;
                                           cfg2 = append_trace cfg1 s la (StepReduce (number p))
                                       in Next cfg2))))
               | Some ActAccept \<Rightarrow>
                   let cfg1 = append_trace cfg s la StepAccept
                   in Done (Accepted (trace cfg1)))))"

inductive reachable_cfg :: "lalr_table \<Rightarrow> token list \<Rightarrow> config \<Rightarrow> bool" where
  reachable_cfg_init:
    "reachable_cfg t toks (init_config t toks)"
| reachable_cfg_next:
    "reachable_cfg t toks cfg
     \<Longrightarrow> one_step t cfg = Next cfg'
     \<Longrightarrow> reachable_cfg t toks cfg'"

lemma step_imp_one_step:
  "step t cfg out \<Longrightarrow> one_step t cfg = out"
    by (induct rule: step.induct)
      (simp_all add: one_step_def top_state_def append_trace_def split: option.splits action.splits)

fun run_detailed_fuel :: "nat \<Rightarrow> lalr_table \<Rightarrow> config \<Rightarrow> run_result option" where
  "run_detailed_fuel 0 t cfg = None"
| "run_detailed_fuel (Suc fuel) t cfg =
    (case one_step t cfg of
      Done r \<Rightarrow> Some r
    | Next cfg' \<Rightarrow> run_detailed_fuel fuel t cfg')"

inductive run_rel :: "lalr_table \<Rightarrow> config \<Rightarrow> run_result \<Rightarrow> nat \<Rightarrow> bool" where
  run_rel_done:
    "one_step t cfg = Done r \<Longrightarrow> run_rel t cfg r (Suc n)"
| run_rel_next:
    "one_step t cfg = Next cfg' \<Longrightarrow> run_rel t cfg' r n \<Longrightarrow>
      run_rel t cfg r (Suc n)"

lemma run_detailed_fuel_to_run_rel:
  assumes "run_detailed_fuel n t cfg = Some r"
  shows "run_rel t cfg r n"
  using assms
proof (induction n arbitrary: cfg)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "one_step t cfg")
    case (Done r0)
    then have "r0 = r"
      using Suc.prems by simp
    then show ?thesis
      using Done run_rel.run_rel_done by simp
  next
    case (Next cfg')
    have "run_detailed_fuel n t cfg' = Some r"
      using Next Suc.prems by simp
    then have "run_rel t cfg' r n"
      using Suc.IH by simp
    then show ?thesis
      using Next run_rel.run_rel_next by meson
  qed
qed

lemma run_rel_to_run_detailed_fuel:
  assumes "run_rel t cfg r n"
  shows "run_detailed_fuel n t cfg = Some r"
  using assms
proof (induction rule: run_rel.induct)
  case (run_rel_done t cfg r)
  then show ?case
    by simp
next
  case (run_rel_next t cfg cfg' r n)
  then show ?case
    by simp
qed

theorem run_detailed_fuel_iff_run_rel:
  "run_detailed_fuel n t cfg = Some r \<longleftrightarrow> run_rel t cfg r n"
proof
  assume "run_detailed_fuel n t cfg = Some r"
  then show "run_rel t cfg r n"
    using run_detailed_fuel_to_run_rel by blast
next
  assume "run_rel t cfg r n"
  then show "run_detailed_fuel n t cfg = Some r"
    using run_rel_to_run_detailed_fuel by blast
qed

definition recognize_detailed :: "nat \<Rightarrow> lalr_table \<Rightarrow> token list \<Rightarrow> run_result option" where
  "recognize_detailed fuel t toks = run_detailed_fuel fuel t (init_config t toks)"

definition recognize :: "nat \<Rightarrow> lalr_table \<Rightarrow> token list \<Rightarrow> bool option" where
  "recognize fuel t toks =
    (case recognize_detailed fuel t toks of
      None \<Rightarrow> None
    | Some (Accepted _) \<Rightarrow> Some True
    | Some (Rejected _ _) \<Rightarrow> Some False)"

end
