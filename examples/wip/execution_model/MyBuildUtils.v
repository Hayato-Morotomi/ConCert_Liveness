From Stdlib Require Import Logic.Decidable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Streams.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.

Section MyBuildUtils.
  Context {BaseTypes : ChainBase}.

  Local Ltac name_deploy_addr :=
    lazymatch goal with
    | H : context [countable.choose ?P ?pf] |- _ =>
        set (to_addr := countable.choose P pf) in *
    end.

  Lemma caddr_not_contract_addr_no_env_contract
      (caddr : Address) (st : ChainState) (wc : WeakContract) :
    reachable st ->
    address_is_contract caddr = false ->
    ~ env_contracts st caddr = Some wc.
  Proof.
    intros reach Haddr deployed.
    enough (address_is_contract caddr = true) by congruence.
    eapply contract_addr_format; eauto.
  Qed.

  Lemma wc_preserve {wc}
            {bstate bstate' : ChainState}
            {caddr} :
    env_contracts bstate caddr = Some wc ->
    ChainTrace bstate bstate' ->
    env_contracts bstate' caddr = Some wc.
  Proof.
    intros deployed trace.
    remember bstate; induction trace; subst; auto.
    specialize_hypotheses.
    clear deployed.
    destruct_chain_step;
      try (rewrite_environment_equiv in *; auto).
    -
      destruct_action_eval.
      * (* transfer *)

        rewrite_environment_equiv in *; auto.
      *
        destruct (address_eqb_spec caddr to_addr); subst; try congruence.
        rewrite_environment_equiv in *; cbn;
          rewrite address_eq_ne; auto.
      *
        rewrite_environment_equiv in *; auto.
    -
      destruct_action_eval.
      * (* transfer *)

        rewrite_environment_equiv in *; auto.
      *
        destruct (address_eqb_spec caddr to_addr); subst; try congruence.
        rewrite_environment_equiv in *; cbn;
          rewrite address_eq_ne; auto.
      *
        rewrite_environment_equiv in *; auto.
  Qed.

  Lemma transfer_balance_same_addr_equiv
        (addr : Address)
        (amount : Amount)
        (env : Environment) :
    EnvironmentEquiv (transfer_balance addr addr amount env) env.
  Proof.
    unfold transfer_balance, add_balance.
    apply build_env_equiv; cbn; repeat intro; auto.
    destruct (address_eqb_spec a addr); subst; lia.
  Qed.

  Lemma filter_build_act_from_ne
        (limit : nat)
        (origin from caddr : Address)
        (acts : list ActionBody) :
    from <> caddr ->
    List.filter
      (fun act => (act_from act =? caddr)%address)
      (List.map (build_act limit origin from) acts) = [].
  Proof.
    intros Hneq.
    induction acts as [|act acts IH]; cbn; auto.
    rewrite address_eq_ne by auto.
    exact IH.
  Qed.

  Lemma deployed_deployment_info_typed
      {Setup Msg State Error : Type}
      `{ser_setup : Serializable Setup} `{ser_msg   : Serializable Msg} `{ser_state : Serializable State} `{ser_error : Serializable Error}
      {contract : Contract Setup Msg State Error}
      {bstate : ChainState} {caddr}
      (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists (dep_info : DeploymentInfo Setup),
      deployment_info Setup trace caddr = Some dep_info.
  Proof.
    intros contract_deployed.
    destruct (deployment_info Setup trace caddr) as [dep_info|] eqn:eq;
      [exists dep_info; auto|].
    trace_induction.
    - cbn in *.
      destruct_action_eval; subst; try name_deploy_addr.
      + (* transfer *)
      rewrite_environment_equiv in *. cbn in *.
      specialize (IH contract_deployed) as (dep_info & dep_some); auto.
      congruence.
    + (* deploy *)
      rewrite_environment_equiv in *. cbn in *.
      destruct (address_eqb_spec caddr to_addr).
      * (* deploy now *)
        destruct ((@deserialize Setup _) setup) eqn: Hsetup.
        -- (* Some *)
          exists (build_deployment_info origin from_addr amount s).
          subst.
          rewrite address_eq_refl in *. congruence.
        -- (* None *)
          cbn in init_some. inversion contract_deployed; subst.
          specialize (wc_init_strong init_some)
            as (setup_strong & result_strong & contra & _).
          congruence.
      * (* already deployed *)
        rewrite address_eq_ne in eq; auto.
    + (* call *)
      rewrite_environment_equiv in *. cbn in *.
      specialize (IH contract_deployed) as (dep_info & dep_some); auto.
      exists dep_info.
      congruence.
    - cbn in *.
      destruct_action_eval; subst; try name_deploy_addr.
      + (* transfer *)
      rewrite_environment_equiv in *. cbn in *.
      specialize (IH contract_deployed) as (dep_info & dep_some); auto.
      congruence.
    + (* deploy *)
      rewrite_environment_equiv in *. cbn in *.
      destruct (address_eqb_spec caddr to_addr).
      * (* deploy now *)
        destruct ((@deserialize Setup _) setup) eqn: Hsetup.
        -- (* Some *)
          exists (build_deployment_info origin from_addr amount s).
          subst.
          rewrite address_eq_refl in *. congruence.
        -- (* None *)
          cbn in init_some. inversion contract_deployed; subst.
          specialize (wc_init_strong init_some)
            as (setup_strong & result_strong & contra & _).
          congruence.
      * (* already deployed *)
        rewrite address_eq_ne in eq; auto.
    + (* call *)
      rewrite_environment_equiv in *. cbn in *.
      specialize (IH contract_deployed) as (dep_info & dep_some); auto.
      exists dep_info.
      congruence.
  Qed.

  Lemma incoming_calls_typed {Setup Msg State Error : Type}
      `{ser_setup : Serializable Setup} `{ser_msg   : Serializable Msg} `{ser_state : Serializable State} `{ser_error : Serializable Error}
       {contract : Contract Setup Msg State Error} {caddr} {bstate}
       (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists inc_calls,
      incoming_calls Msg trace caddr = Some inc_calls.
  Proof.
    intros * deployed.
    trace_induction; cbn.
    - destruct_action_eval; try rewrite_environment_equiv in *; subst; cbn in *; try name_deploy_addr.
      + destruct (IH deployed) as (inc_calls & ?). exists inc_calls. auto.
      + destruct (address_eqb_spec to_addr caddr) as [->|].
        * rewrite address_eq_refl in deployed. inversion deployed; subst.
          exists [].
          eapply undeployed_contract_no_in_calls; auto.
        * rewrite address_eq_ne in deployed; auto.
      + destruct (address_eqb_spec to_addr caddr); subst; auto.
        rewrite address_eq_refl in *.
        rewrite deployed in *. inversion deployed0; subst.
        destruct (IH ltac:(auto)) as (inc_calls & Hinc).
        apply (wc_receive_strong) in receive_some
         as (prev_state_strong & msg_strong & new_state_strong & ? & ? & ? & receive_some).
        exists ({| call_limit := limit; call_origin := origin; call_from := from_addr; call_amount := amount; call_msg := msg_strong |}
                  :: inc_calls).
        destruct msg.
        * destruct msg_strong; try congruence. cbn in *.
          rewrite H0.
          rewrite Hinc. auto.
        * destruct msg_strong; cbn in *; try congruence.
          now rewrite Hinc.
    - destruct_action_eval; try rewrite_environment_equiv in *; subst; cbn in *; try name_deploy_addr.
      + destruct (IH deployed) as (inc_calls & ?). exists inc_calls. auto.
      + destruct (address_eqb_spec to_addr caddr) as [->|].
        * rewrite address_eq_refl in deployed. inversion deployed; subst.
          exists [].
          eapply undeployed_contract_no_in_calls; auto.
        * rewrite address_eq_ne in deployed; auto.
      + destruct (address_eqb_spec to_addr caddr); subst; auto.
        rewrite address_eq_refl in *.
        rewrite deployed in *. inversion deployed0; subst.
        destruct (IH ltac:(auto)) as (inc_calls & Hinc).
        apply (wc_receive_strong) in receive_some
         as (prev_state_strong & msg_strong & new_state_strong & ? & ? & ? & receive_some).
        exists ({| call_limit := limit; call_origin := origin; call_from := from_addr; call_amount := amount; call_msg := msg_strong |}
                  :: inc_calls).
        destruct msg.
        * destruct msg_strong; try congruence. cbn in *.
          rewrite H0.
          rewrite Hinc. auto.
        * destruct msg_strong; cbn in *; try congruence.
          now rewrite Hinc.
  Qed.

  Lemma deployed_typed {Setup Msg State Error : Type}
      `{ser_setup : Serializable Setup} `{ser_msg   : Serializable Msg} `{ser_state : Serializable State} `{ser_error : Serializable Error}
       {contract : Contract Setup Msg State Error} {caddr} {st}
       (trace : ChainTrace empty_state st) :
    env_contracts st caddr = Some (contract : WeakContract) ->
    exists (dep : DeploymentInfo Setup) (cstate : State) (inc : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some dep /\
      contract_state st caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc.
  Proof.
    intros deployed.
    assert (reach : reachable st).
    { constructor; auto. }
    specialize (deployed_contract_state_typed deployed reach)
      as (cstate & deployed_cstate).
    specialize (deployed_deployment_info_typed trace deployed)
      as (dep_info & Hdep_info).
    specialize (incoming_calls_typed trace deployed)
      as (inc_calls & Hinc_calls).
    exists dep_info, cstate, inc_calls.
    repeat (split; auto).
  Qed.

  Lemma incoming_calls_app {Msg : Type}  `{msg_ser : Serializable Msg}
        {caddr} {st1 st2 st3} {trace12 : ChainTrace st1 st2} {trace23 : ChainTrace st2 st3}
        (inc_calls1 inc_calls2 : list (ContractCallInfo Msg)) :
    incoming_calls Msg trace12 caddr = Some inc_calls1 ->
    incoming_calls Msg trace23 caddr = Some inc_calls2 ->
    incoming_calls Msg (clist_app trace12 trace23) caddr = Some (inc_calls2 ++ inc_calls1).
  Proof.
    generalize dependent inc_calls2.
    generalize dependent inc_calls1.
    remember st2; induction trace23; subst; intros.
    cbn in *. inversion H0. subst. auto.
    cbn.
    destruct_chain_step; auto.
    -
      cbn in *.
      destruct (incoming_calls Msg trace23 caddr) eqn:H23.
      2:{
        destruct_action_eval; try congruence.
        destruct_address_eq; subst; try congruence.
        destruct msg; destruct_match; try congruence.
      }
      erewrite IHtrace23; eauto.
      destruct_action_eval; try congruence.
      destruct_address_eq; subst; try congruence.
      destruct msg as [m|]; try destruct (deserialize m); try congruence.
      + inversion H0; subst. auto.
      + inversion H0; subst; auto.
    -
      cbn in *.
      destruct (incoming_calls Msg trace23 caddr) eqn:H23.
      2:{
        destruct_action_eval; try congruence.
        destruct_address_eq; subst; try congruence.
        destruct msg; destruct_match; try congruence.
      }
      erewrite IHtrace23; eauto.
      destruct_action_eval; try congruence.
      destruct_address_eq; subst; try congruence.
      destruct msg as [m|]; try destruct (deserialize m); try congruence.
      + inversion H0; subst. auto.
      + inversion H0; subst; auto.
  Qed.

  Open Scope Z_scope.

  Lemma exist_step_call : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                bstate limit origin from caddr amount msg acts new_acts
                                (cstate new_cstate : State),
    reachable bstate ->
    chain_state_queue bstate = {| act_limit := limit;
                                  act_from := from;
                                  act_origin := origin;
                                  act_body := act_call caddr amount ((@serialize Msg _) msg) |} :: acts ->
    (0 < limit)%nat ->
    (amount >= 0)%Z ->
    (amount <= env_account_balances bstate from)%Z ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    receive contract (transfer_balance from caddr amount bstate)
                      (build_ctx limit origin from caddr (if (address_eqb from caddr)
                        then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount) amount)
                      cstate (Some msg) = Ok (new_cstate, new_acts) ->
    (exists (bstate' : ChainState),
    inhabited (ActionEvaluation bstate
        {| act_limit := limit;
          act_from := from;
          act_origin := origin;
          act_body := act_call caddr amount ((@serialize Msg _) msg) |}
        bstate' (List.map (build_act (limit - 1) origin caddr) new_acts))
    /\ chain_state_queue bstate' = (List.map (build_act (limit - 1) origin caddr) new_acts) ++ acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr (serialize new_cstate) (transfer_balance from caddr amount bstate))).
  Proof.
    intros * reach queue enough_limit amount_nonnegative enough_balance
      deployed deployed_state receive_some.
    pose (new_to_balance := if (address_eqb from caddr)
                          then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount).
    pose (bstate' := (bstate<|chain_state_queue := (List.map (build_act (limit - 1) origin caddr) new_acts) ++ acts|>
                            <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                    (transfer_balance from caddr amount bstate)|>)).
    assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance) by
    (cbn; destruct_address_eq; easy).
    exists bstate'.
    do 2 split. 2: auto. 2: reflexivity.
    cbn in deployed_state.
    destruct (env_contract_states bstate caddr) eqn:Hstate; try congruence.
      eapply eval_call with (msg := Some ((@serialize Msg _) msg))
        (prev_state := s); eauto.
      -
        apply wc_receive_to_receive' with (cstate := cstate); auto.
        rewrite new_to_balance_eq.
        apply receive_some.
      - constructor; reflexivity.
  Qed.

End MyBuildUtils.