From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.
From Stdlib Require Import Logic.Decidable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepDetermin.

Local Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
  end.
Local Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

Section ChainStepSerial.
  Context {BaseTypes : ChainBase}.

Section ActionEvaluationDecidable.

  Lemma eval_limit_exact : forall st act next_st new_acts,
    ActionEvaluation st act next_st new_acts ->
    Forall (fun a => act_limit a = (act_limit act - 1)%nat) new_acts.
  Proof.
    intros st act next_st new_acts Heval.
    destruct Heval; subst; cbn; try constructor.
    apply All_Forall.Forall_map.
    apply Forall_forall.
    intros x Hx.
    reflexivity.
  Qed.

  Open Scope Z_scope.

  Ltac action_not_decidable :=
    right; intro;
    match goal with
    | H : exists bstate new_acts,
          inhabited (ActionEvaluation _ _ bstate new_acts) |- False =>
      destruct H as [bstate_new [new_acts [action_evaluation]]];
      destruct_action_eval; try congruence
    end; repeat
    match goal with
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} =
          {| act_limit := _; act_origin := _; act_from := _;
             act_body := match ?msg with | Some _ => _ | None => _ end |} |- False =>
      destruct msg
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} =
          {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} |- False =>
      inversion H; subst; clear H
    end.

  Local Ltac action_decidable :=
    left; do 2 eexists; constructor;
    match goal with
    | H : wc_receive _ _ _ _ ?m = Ok _ |- _ => eapply eval_call with (msg := m)
    | H : wc_init _ _ _ _ = Ok _ |- _ => eapply eval_deploy
    | H : context [act_transfer _ _] |- _ => eapply eval_transfer
    end;
    eauto; try reflexivity.

  Local Ltac rewrite_balance :=
    match goal with
    | H := context [if (_ =? ?to)%address then _ else _],
      H2 : Environment |- _ =>
      assert (new_to_balance_eq : env_account_balances H2 to = H);
      [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
        now rewrite <- new_to_balance_eq in * ]
    end.

  Lemma action_evaluation_decidable_action_trace : forall from bstate act,
    reachable_action_trace from bstate ->
    decidable (exists new_env new_acts,
      inhabited (ActionEvaluation bstate act new_env new_acts)).
  Proof.
    intros * Hreach.
    destruct act eqn:Hact.
    destruct act_body;
      (destruct (amount >=? 0) eqn:amount_positive;
      [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
        action_not_decidable; now rewrite Z.geb_leb, Z.leb_gt in amount_positive];
      [| action_not_decidable; now rewrite Z.leb_gt in balance]);
    try (destruct (address_is_contract to) eqn:to_is_contract;
      [destruct (env_contracts bstate to) eqn:to_contract;
       [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
    try now action_not_decidable.
    all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
    all : rewrite Z.leb_le in balance.
    - (* act_body = act_transfer to amount, evaluated as a contract call *)
      pose (new_to_balance :=
        if address_eqb act_from to
        then env_account_balances bstate to
        else env_account_balances bstate to + amount).
      destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_limit act_origin act_from to new_to_balance amount)
        s None) eqn:receive.
      + destruct t.
        pose (bstate' :=
          set_contract_state to s0
            (transfer_balance act_from to amount bstate)).
        destruct (Nat.ltb_spec 0 act_limit)%nat.
        * action_decidable.
          rewrite_balance.
        * action_not_decidable; lia.
      + action_not_decidable.
        rewrite_balance.
    - (* act_body = act_transfer to amount, evaluated as a simple transfer *)
      pose (bstate' := transfer_balance act_from to amount bstate).
      destruct (Nat.ltb_spec 0 act_limit)%nat.
      + action_decidable.
      + action_not_decidable; lia.
    - (* act_body = act_call to amount msg *)
      pose (new_to_balance :=
        if address_eqb act_from to
        then env_account_balances bstate to
        else env_account_balances bstate to + amount).
      destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_limit act_origin act_from to new_to_balance amount)
        s (Some msg)) eqn:receive.
      + destruct t.
        pose (bstate' :=
          set_contract_state to s0
            (transfer_balance act_from to amount bstate)).
        destruct (Nat.ltb_spec 0 act_limit)%nat.
        * action_decidable.
          rewrite_balance.
        * action_not_decidable; lia.
      + action_not_decidable.
        rewrite_balance.
    - (* act_body = act_call to amount msg, but [to] is not a valid contract. *)
      action_not_decidable.
      pose proof (contract_addr_format_in_action_trace to_addr wc Hreach deployed).
      congruence.
    - (* act_body = act_deploy amount c setup *)
      destruct (BuildUtils.fresh_address_exists_decidable bstate)
        as [fresh_addr_some | no_fresh_addr].
      + (* The deployed address is uniquely determined by countable.choose *)
        pose (to := countable.choose (fresh_address bstate) fresh_addr_some).
        destruct (wc_init c
                    (transfer_balance act_from to amount bstate)
                    (build_ctx act_limit act_origin act_from to amount amount)
                    setup) as [state | err] eqn:init.
        * destruct (Nat.ltb_spec 0 act_limit)%nat.
          -- (* Case: act_deploy is evaluable by eval_deploy *)
             left. do 2 eexists. constructor.
             eapply (eval_deploy act_limit act_origin act_from to amount c setup state
                       ltac:(lia) amount_positive balance fresh_addr_some eq_refl eq_refl init);
               reflexivity.
          -- action_not_decidable; lia.
        * (* Case: wc_init failed at the chosen address *)
          action_not_decidable.
          (* Any fresh-address proof yields the same address (choose_pi) *)
          rewrite (countable.choose_pi _ fresh_addr_some0 fresh_addr_some) in init_some.
          fold to in init_some.
          congruence.
      + (* Case: there is no fresh contract address *)
        now action_not_decidable.
  Qed.

  Close Scope Z_scope.

End ActionEvaluationDecidable.

Section ActionChainFinishOrFail.

  Lemma action_finish_or_fail : forall (n : nat) (from st : ChainState)
      (acts1 acts2 : list Action),
    reachable_action_trace from st ->
    Forall (fun act => act_limit act = n) acts1 ->
    st.(chain_state_queue) = acts1 ++ acts2 ->
    (exists finish_bstate,
      finish_bstate.(chain_state_queue) = acts2 /\
      inhabited (ActionChainTrace st finish_bstate)) \/
    (exists fail_bstate act acts1',
      inhabited (ActionChainTrace st fail_bstate) /\
      fail_bstate.(chain_state_queue) = act :: acts1' ++ acts2 /\
      (forall new_env new_acts,
        ActionEvaluation fail_bstate act new_env new_acts -> False)).
  Proof.
    induction n as [|n' IHn']; intros from st acts1.
    - intros acts2 Hreach Hlimits Hqueue.
      destruct acts1 as [|act1 acts1'].
      + left.
        exists st.
        split; [exact Hqueue|].
        constructor. apply clnil.
      + right.
        exists st, act1, acts1'.
        split.
        * constructor. apply clnil.
        * split.
          -- exact Hqueue.
          -- intros next_bstate new_acts Heval.
             apply Forall_cons_iff in Hlimits as [Hlimit _].
             destruct Heval; subst; cbn in Hlimit; lia.
    - generalize dependent from.
      generalize dependent st.
      induction acts1 as [|act1 acts1' IHacts1'];
        intros st from acts2 Hreach Hlimits Hqueue.
      + left.
        exists st.
        split; [exact Hqueue|].
        constructor. apply clnil.
      + apply Forall_cons_iff in Hlimits as [Hlimit_act1 Hlimits_tail].
        cbn in Hqueue.
        destruct (action_evaluation_decidable_action_trace from st act1 Hreach)
          as [(next_env & new_acts & [Heval]) | Hnoeval].
        * assert (Hnew_limits :
              Forall (fun act => act_limit act = n') new_acts).
          {
            pose proof
              (eval_limit_exact st act1 next_env new_acts Heval)
              as Hlimits_new.
            eapply Forall_impl; [| exact Hlimits_new].
            intros a Ha.
            rewrite Hlimit_act1 in Ha.
            lia.
          }
          pose (next_st := build_chain_state next_env (new_acts ++ acts1' ++ acts2)).
          assert (Hstep : ActionChainStep st next_st).
          {
            subst next_st.
            eapply action_step
              with (act := act1)
                   (acts := acts1' ++ acts2)
                   (new_acts := new_acts).
            - exact Hqueue.
            - exact Heval.
            - reflexivity.
          }
          assert (Hreach_next : reachable_action_trace from next_st).
          {
            eapply reachable_action_trace_step; eauto.
          }
          destruct
            (IHn' from next_st new_acts (acts1' ++ acts2)
               Hreach_next Hnew_limits eq_refl)
            as [(finish_new & Hqueue_finish_new & [trace_new]) |
                (fail_bstate & fail_act & fail_acts & [trace_fail] &
                 Hqueue_fail & Hnoeval_fail)].
          -- assert (Hreach_finish_new :
                  reachable_action_trace from finish_new).
             {
               eapply reachable_action_trace_trans; eauto.
             }
             destruct
               (IHacts1' finish_new from acts2 Hreach_finish_new
                  Hlimits_tail Hqueue_finish_new)
               as [(finish_bstate & Hqueue_finish & [trace_finish_tail]) |
                   (fail_bstate & fail_act & fail_acts & [trace_fail_tail] &
                    Hqueue_fail & Hnoeval_fail)].
             ++ left.
                exists finish_bstate.
                split; [exact Hqueue_finish|].
                destruct (action_trace_step_trace Hstep trace_new)
                  as [trace_st_finish_new].
                destruct (action_trace_trans trace_st_finish_new trace_finish_tail)
                  as [trace_st_finish].
                constructor.
                exact trace_st_finish.
             ++ right.
                exists fail_bstate, fail_act, fail_acts.
                split.
                ** destruct (action_trace_step_trace Hstep trace_new)
                     as [trace_st_finish_new].
                   destruct (action_trace_trans trace_st_finish_new trace_fail_tail)
                     as [trace_st_fail].
                   constructor.
                   exact trace_st_fail.
                ** split; assumption.
          -- right.
             exists fail_bstate, fail_act, (fail_acts ++ acts1').
             split.
             ++ destruct (action_trace_step_trace Hstep trace_fail)
                  as [trace_st_fail].
                constructor.
                exact trace_st_fail.
             ++ split.
                ** rewrite Hqueue_fail.
                   rewrite app_assoc.
                   reflexivity.
                ** exact Hnoeval_fail.
        * right.
          exists st, act1, acts1'.
          split.
          -- constructor. apply clnil.
          -- split.
             ++ exact Hqueue.
             ++ intros next_bstate new_acts Heval.
                apply Hnoeval.
                exists next_bstate, new_acts.
                constructor.
                exact Heval.
  Qed.

  Lemma one_action_finish_or_fail : forall (from st : ChainState)
      (act : Action) (acts : list Action),
    reachable_action_trace from st ->
    st.(chain_state_queue) = act :: acts ->
    (exists finish_bstate,
      finish_bstate.(chain_state_queue) = acts /\
      inhabited (ActionChainTrace st finish_bstate)) \/
    (exists fail_bstate act' acts',
      inhabited (ActionChainTrace st fail_bstate) /\
      fail_bstate.(chain_state_queue) = act' :: acts' ++ acts /\
      (forall new_env new_acts,
        ActionEvaluation fail_bstate act' new_env new_acts -> False)).
  Proof.
    intros from st act acts Hreach Hqueue.
    replace (act :: acts) with ([act] ++ acts) in Hqueue by reflexivity.
    eapply (action_finish_or_fail (act_limit act) from st [act] acts); eauto.
  Qed.

End ActionChainFinishOrFail.

  Class ChainBaseHasUser : Prop :=
    user_address_exists : exists (user : Address), address_is_contract user = false.

  Context {HasUser : ChainBaseHasUser}.

  (* serialization [totality] of the ActionChainTrace-based ChainStep *)
  Lemma chain_step_serial : forall st : ChainState,
    reachable st ->
    exists st', inhabited (ChainStep st st').
  Proof.
    intros st Hreach.
    destruct (chain_state_queue st) as [|act acts] eqn:Hqueue.
    - (* queue = [] : block step *)
      destruct user_address_exists as (creator & Hcreator_account).
      (* The next block is built directly (forward_time from BlockchainBuilder is not needed) *)
      pose (header := build_block_Header
                        (S (chain_height st)) (S (current_slot st))
                        (finalized_height st) 0 creator).
      exists (build_chain_state (add_new_block_to_env header st) []).
      constructor.
      apply (step_block st _ header); cbn; auto.
      + pose proof (finalized_heigh_chain_height st Hreach).
        constructor; cbn; auto; lia.
      + reflexivity.
    - (* queue = act :: acts *)
      destruct (address_is_contract act.(act_from)) eqn:Hfrom.
      + (* head action is from a contract: it must be evaluable. *)
        destruct (act_from_contract_eval st act acts Hreach Hqueue Hfrom)
          as (next_env & new_acts & [Heval]).
        exists (build_chain_state next_env (new_acts ++ acts)).
        constructor.
        eapply step_action_contract
          with (act := act)
               (acts := acts)
               (new_acts := new_acts).
        * exact Hqueue.
        * exact Heval.
        * reflexivity.
        * unfold act_is_from_contract.
          exact Hfrom.
      + (* head action is from an account. *)
        pose proof (reachable_action_trace_refl Hreach) as Hreach_trace.
        destruct (one_action_finish_or_fail st st act acts Hreach_trace Hqueue)
          as [(finish_bstate & Hqueue_finish & [trace_finish]) |
              (fail_bstate & fail_act & fail_acts & [trace_fail] &
               Hqueue_fail & Hnoeval)].
        * (* The action chain reaches exactly the queue tail; the first
             ActionChainStep gives the user action step. *)
          destruct (action_trace_step trace_finish)
            as [Heq_finish | (next_bstate & [Hstep] & Htrace_tail)].
          -- subst finish_bstate.
             rewrite Hqueue in Hqueue_finish.
             apply (f_equal (@length Action)) in Hqueue_finish.
             cbn in Hqueue_finish.
             lia.
          -- destruct Hstep as [act0 acts0 new_acts Hqueue_step Heval Hqueue_next].
             rewrite Hqueue in Hqueue_step.
             inversion Hqueue_step; subst act0 acts0; clear Hqueue_step.
             exists next_bstate.
             constructor.
             eapply step_action_user
               with (act := act)
                    (acts := acts)
                    (new_acts := new_acts)
                    (finish_bstate := finish_bstate).
             ++ exact Hqueue.
             ++ exact Heval.
             ++ exact Hqueue_next.
             ++ unfold act_is_from_account.
                exact Hfrom.
             ++ exact trace_finish.
             ++ exact Hqueue_finish.
        * (* The action chain gets stuck before reaching the queue tail. *)
          exists (build_chain_state st.(chain_state_env) acts).
          constructor.
          eapply step_action_invalid
            with (act := act)
                 (acts := acts)
                 (fail_bstate := fail_bstate)
                 (act' := fail_act)
                 (acts' := fail_acts).
          -- reflexivity.
          -- exact Hqueue.
          -- reflexivity.
          -- unfold act_is_from_account.
             exact Hfrom.
          -- exact trace_fail.
          -- exact Hqueue_fail.
          -- exact Hnoeval.
  Qed.

End ChainStepSerial.

Section ChainStepSerialType.
  Context {BaseTypes : ChainBase}.

  Class ChainBaseFreshDec : Type :=
    fresh_address_exists_dec :
      forall env : Environment, {exists a, fresh_address env a} + {~ exists a, fresh_address env a}.

  Context {FreshDec : ChainBaseFreshDec}.

  Definition EvalResult (st : ChainState) (act : Action) : Type :=
    ({ next_env : Environment & { new_acts : list Action & ActionEvaluation st act next_env new_acts } }
     + (forall next_env new_acts, ActionEvaluation st act next_env new_acts -> False))%type.

  Open Scope Z_scope.

  Local Ltac action_not_decidable_T :=
    right; intros bstate_new new_acts action_evaluation;
    destruct_action_eval; try congruence;
    repeat
    match goal with
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} =
          {| act_limit := _; act_origin := _; act_from := _;
             act_body := match ?msg with | Some _ => _ | None => _ end |} |- False =>
      destruct msg
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} =
          {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} |- False =>
      inversion H; subst; clear H
    end.

  Local Ltac action_decidable_T :=
    left; do 2 eexists;
    match goal with
    | H : wc_receive _ _ _ _ ?m = Ok _ |- _ => eapply eval_call with (msg := m)
    | H : wc_init _ _ _ _ = Ok _ |- _ => eapply eval_deploy
    | H : context [act_transfer _ _] |- _ => eapply eval_transfer
    end;
    eauto; try reflexivity.

  Local Ltac rewrite_balance_T :=
    match goal with
    | H := context [if (_ =? ?to)%address then _ else _],
      H2 : Environment |- _ =>
      assert (new_to_balance_eq : env_account_balances H2 to = H);
      [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
        now rewrite <- new_to_balance_eq in * ]
    end.

  Lemma action_evaluation_dec : forall from bstate act,
    reachable_action_trace from bstate ->
    EvalResult bstate act.
  Proof.
    intros * Hreach.
    destruct act eqn:Hact.
    destruct act_body;
      (destruct (amount >=? 0) eqn:amount_positive;
      [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
        action_not_decidable_T; now rewrite Z.geb_leb, Z.leb_gt in amount_positive];
      [| action_not_decidable_T; now rewrite Z.leb_gt in balance]);
    try (destruct (address_is_contract to) eqn:to_is_contract;
      [destruct (env_contracts bstate to) eqn:to_contract;
       [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
    try now action_not_decidable_T.
    all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
    all : rewrite Z.leb_le in balance.
    - pose (new_to_balance :=
        if address_eqb act_from to
        then env_account_balances bstate to
        else env_account_balances bstate to + amount).
      destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_limit act_origin act_from to new_to_balance amount)
        s None) eqn:receive.
      + destruct t.
        pose (bstate' :=
          set_contract_state to s0
            (transfer_balance act_from to amount bstate)).
        destruct (Nat.ltb_spec0 0 act_limit)%nat.
        * action_decidable_T.
          rewrite_balance_T.
        * action_not_decidable_T; lia.
      + action_not_decidable_T.
        rewrite_balance_T.
    - pose (bstate' := transfer_balance act_from to amount bstate).
      destruct (Nat.ltb_spec0 0 act_limit)%nat.
      + action_decidable_T.
      + action_not_decidable_T; lia.
    - pose (new_to_balance :=
        if address_eqb act_from to
        then env_account_balances bstate to
        else env_account_balances bstate to + amount).
      destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_limit act_origin act_from to new_to_balance amount)
        s (Some msg)) eqn:receive.
      + destruct t.
        pose (bstate' :=
          set_contract_state to s0
            (transfer_balance act_from to amount bstate)).
        destruct (Nat.ltb_spec0 0 act_limit)%nat.
        * action_decidable_T.
          rewrite_balance_T.
        * action_not_decidable_T; lia.
      + action_not_decidable_T.
        rewrite_balance_T.
    - action_not_decidable_T.
      pose proof (contract_addr_format_in_action_trace to_addr wc Hreach deployed).
      congruence.
    - destruct (fresh_address_exists_dec bstate) as [fresh_addr_some | no_fresh_addr].
      + pose (to := countable.choose (fresh_address bstate) fresh_addr_some).
        destruct (wc_init c
                    (transfer_balance act_from to amount bstate)
                    (build_ctx act_limit act_origin act_from to amount amount)
                    setup) as [state | err] eqn:init.
        * destruct (Nat.ltb_spec0 0 act_limit)%nat.
          -- left. do 2 eexists.
             eapply (eval_deploy act_limit act_origin act_from to amount c setup state
                       ltac:(lia) amount_positive balance fresh_addr_some eq_refl eq_refl init);
               reflexivity.
          -- action_not_decidable_T; lia.
        * action_not_decidable_T.
          rewrite (countable.choose_pi _ fresh_addr_some0 fresh_addr_some) in init_some.
          fold to in init_some.
          congruence.
      + now action_not_decidable_T.
  Qed.

  Close Scope Z_scope.

  Lemma action_finish_or_fail_T : forall (n : nat) (from st : ChainState)
      (acts1 acts2 : list Action),
    reachable_action_trace from st ->
    Forall (fun act => act_limit act = n) acts1 ->
    st.(chain_state_queue) = acts1 ++ acts2 ->
    ({ finish_bstate : ChainState &
       (finish_bstate.(chain_state_queue) = acts2) * ActionChainTrace st finish_bstate } +
     { fail_bstate : ChainState & { act : Action & { acts1' : list Action &
       (ActionChainTrace st fail_bstate *
        (fail_bstate.(chain_state_queue) = act :: acts1' ++ acts2) *
        (forall new_env new_acts, ActionEvaluation fail_bstate act new_env new_acts -> False)) } } })%type.
  Proof.
    induction n as [|n' IHn']; intros from st acts1.
    - intros acts2 Hreach Hlimits Hqueue.
      destruct acts1 as [|act1 acts1'].
      + left. exists st. split; [exact Hqueue|exact clnil].
      + right. exists st, act1, acts1'.
        split; [split; [exact clnil|exact Hqueue]|].
        intros next_bstate new_acts Heval.
        apply Forall_cons_iff in Hlimits as [Hlimit _].
        destruct Heval; subst; cbn in Hlimit; lia.
    - generalize dependent from.
      generalize dependent st.
      induction acts1 as [|act1 acts1' IHacts1'];
        intros st from acts2 Hreach Hlimits Hqueue.
      + left. exists st. split; [exact Hqueue|exact clnil].
      + assert (Hlimit_act1 : act_limit act1 = S n') by (inversion Hlimits; auto).
        assert (Hlimits_tail : Forall (fun act => act_limit act = S n') acts1') by (inversion Hlimits; auto).
        cbn in Hqueue.
        destruct (action_evaluation_dec from st act1 Hreach)
          as [(next_env & new_acts & Heval) | Hnoeval].
        * assert (Hnew_limits : Forall (fun act => act_limit act = n') new_acts).
          { pose proof (eval_limit_exact st act1 next_env new_acts Heval) as Hlimits_new.
            eapply Forall_impl; [| exact Hlimits_new].
            intros a Ha. rewrite Hlimit_act1 in Ha. lia. }
          pose (next_st := build_chain_state next_env (new_acts ++ acts1' ++ acts2)).
          assert (Hstep : ActionChainStep st next_st).
          { subst next_st.
            eapply action_step with (act := act1) (acts := acts1' ++ acts2) (new_acts := new_acts).
            - exact Hqueue.
            - exact Heval.
            - reflexivity. }
          assert (Hreach_next : reachable_action_trace from next_st)
            by (eapply reachable_action_trace_step; eauto).
          destruct (IHn' from next_st new_acts (acts1' ++ acts2) Hreach_next Hnew_limits eq_refl)
            as [(finish_new & Hqueue_finish_new & trace_new) |
                (fail_bstate & fail_act & fail_acts & ((trace_fail & Hqueue_fail) & Hnoeval_fail))].
          -- assert (Hreach_finish_new : reachable_action_trace from finish_new)
               by (eapply reachable_action_trace_trans; eauto).
             destruct (IHacts1' finish_new from acts2 Hreach_finish_new Hlimits_tail Hqueue_finish_new)
               as [(finish_bstate & Hqueue_finish & trace_finish_tail) |
                   (fail_bstate & fail_act & fail_acts & ((trace_fail_tail & Hqueue_fail) & Hnoeval_fail))].
             ++ left. exists finish_bstate.
                split; [exact Hqueue_finish|].
                exact (clist_app (clist_app (snoc clnil Hstep) trace_new) trace_finish_tail).
             ++ right. exists fail_bstate, fail_act, fail_acts.
                split; [split|].
                ** exact (clist_app (clist_app (snoc clnil Hstep) trace_new) trace_fail_tail).
                ** exact Hqueue_fail.
                ** exact Hnoeval_fail.
          -- right. exists fail_bstate, fail_act, (fail_acts ++ acts1').
             split; [split|].
             ++ exact (clist_app (snoc clnil Hstep) trace_fail).
             ++ rewrite Hqueue_fail, app_assoc. reflexivity.
             ++ exact Hnoeval_fail.
        * right. exists st, act1, acts1'.
          split; [split; [exact clnil|exact Hqueue]|].
          exact Hnoeval.
  Qed.

  Fixpoint action_trace_first {a b : ChainState} (tr : ActionChainTrace a b)
      : ((a = b) + { m : ChainState & (ActionChainStep a m * ActionChainTrace m b)%type })%type :=
    match tr with
    | clnil => inl eq_refl
    | snoc tr' l =>
        match action_trace_first tr' with
        | inl e => inr (existT _ (eq_rect_r (fun x => ActionChainStep x _) l e, clnil))
        | inr (existT m (s, t)) => inr (existT m (s, snoc t l))
        end
    end.

  Context {HasUser : ChainBaseHasUser}.

  Local Instance is_account_dec : forall a : Address, base.Decision (address_is_contract a = false) :=
    fun a => Bool.bool_dec (address_is_contract a) false.

  Definition some_user : Address :=
    countable.choose (fun a => address_is_contract a = false) user_address_exists.

  Lemma some_user_account : address_is_contract some_user = false.
  Proof. apply (countable.choose_correct (fun a => address_is_contract a = false)). Qed.

  Lemma chain_step_serial_T : forall st : ChainState,
    reachable st -> { st' : ChainState & ChainStep st st' }.
  Proof.
    intros st Hreach.
    destruct (chain_state_queue st) as [|act acts] eqn:Hqueue.
    - pose (header := build_block_Header
                        (S (chain_height st)) (S (current_slot st))
                        (finalized_height st) 0 some_user).
      exists (build_chain_state (add_new_block_to_env header st) []).
      apply (step_block st _ header); cbn; auto.
      + pose proof (finalized_heigh_chain_height st Hreach).
        pose proof some_user_account.
        constructor; cbn; auto; lia.
      + reflexivity.
    - destruct (address_is_contract act.(act_from)) eqn:Hfrom.
      + destruct (action_evaluation_dec st st act (reachable_action_trace_refl Hreach))
          as [(next_env & new_acts & Heval) | Hnoeval].
        * exists (build_chain_state next_env (new_acts ++ acts)).
          eapply step_action_contract with (act := act) (acts := acts) (new_acts := new_acts).
          -- exact Hqueue.
          -- exact Heval.
          -- reflexivity.
          -- exact Hfrom.
        * exfalso.
          destruct (act_from_contract_eval st act acts Hreach Hqueue Hfrom)
            as (next_env & new_acts & [Heval]).
          exact (Hnoeval _ _ Heval).
      + pose proof (reachable_action_trace_refl Hreach) as Hreach_trace.
        replace (act :: acts) with ([act] ++ acts) in Hqueue by reflexivity.
        destruct (action_finish_or_fail_T (act_limit act) st st [act] acts Hreach_trace
                    ltac:(repeat constructor) Hqueue)
          as [(finish_bstate & Hqueue_finish & trace_finish) |
              (fail_bstate & fail_act & fail_acts & ((trace_fail & Hqueue_fail) & Hnoeval))];
          cbn in Hqueue.
        * destruct (action_trace_first trace_finish)
            as [Heq_finish | (next_bstate & (Hstep & Htrace_tail))].
          -- exfalso. subst finish_bstate.
             rewrite Hqueue in Hqueue_finish.
             apply (f_equal (@length Action)) in Hqueue_finish.
             cbn in Hqueue_finish. lia.
          -- destruct Hstep as [act0 acts0 new_acts Hqueue_step Heval Hqueue_next].
             rewrite Hqueue in Hqueue_step.
             assert (act0 = act /\ acts0 = acts) as [-> ->] by (inversion Hqueue_step; auto).
             exists next_bstate.
             eapply step_action_user
               with (act := act) (acts := acts) (new_acts := new_acts) (finish_bstate := finish_bstate).
             ++ exact Hqueue.
             ++ exact Heval.
             ++ exact Hqueue_next.
             ++ exact Hfrom.
             ++ exact trace_finish.
             ++ exact Hqueue_finish.
        * exists (build_chain_state st.(chain_state_env) acts).
          eapply step_action_invalid
            with (act := act) (acts := acts) (fail_bstate := fail_bstate)
                 (act' := fail_act) (acts' := fail_acts).
          -- reflexivity.
          -- exact Hqueue.
          -- reflexivity.
          -- exact Hfrom.
          -- exact trace_fail.
          -- exact Hqueue_fail.
          -- exact Hnoeval.
  Qed.

End ChainStepSerialType.
