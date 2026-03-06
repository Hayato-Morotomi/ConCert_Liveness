From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import ZArith.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.

Ltac inversion_subst H :=
  inversion H; subst; clear H.

Section BuildUtils.
  Context {BaseTypes : ChainBase}.

  Lemma reachable_empty_state :
    reachable empty_state.
  Proof.
    repeat constructor.
  Qed.

  (* Transitivity property of reachable and ChainTrace *)
  Lemma reachable_trans from to :
    reachable from -> ChainTrace from to -> reachable to.
  Proof.
    intros [].
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  (* Transitivity property of reachable and ChainStep *)
  Lemma reachable_step from to :
    reachable from -> ChainStep from to -> reachable to.
  Proof.
    intros [].
    now do 2 econstructor.
  Qed.

  (* If a state is reachable then the finalized_height cannot be larger than the chain_height *)
  Lemma finalized_heigh_chain_height bstate :
    reachable bstate ->
    finalized_height bstate < S (chain_height bstate).
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ]; subst.
    - auto.
    - destruct_chain_step; try rewrite_environment_equiv; auto.
      + now inversion valid_header.
      + (* action *)
        assert (A: forall st, ActionChainTrace from st -> finalized_height st < S (chain_height st)).
        {
          intros * trace'. remember from; induction trace'; subst; auto.
          destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv; auto.
        }
        auto.
  Qed.

  (* If a state is reachable and contract state is stored on an address
    then that address must also have some contract deployed to it *)
  Lemma contract_states_deployed to (addr : Address) (state : SerializedValue) :
    reachable to ->
    env_contract_states to addr = Some state ->
    exists wc, env_contracts to addr = Some wc.
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ];
      subst; intros.
    - discriminate.
    - destruct_chain_step.
      + (* add_block *)
        rewrite_environment_equiv. specialize_hypotheses. destruct IH as (wc & deployed).
        exists wc. rewrite_environment_equiv. cbn. auto.
      + (* action *)
        assert (at_contract_states_deployed : 
          forall st,
            ActionChainTrace from st ->
            env_contract_states st addr = Some state ->
            exists wc, env_contracts st addr = Some wc).
        {
          intros * action_trace'.
          (* generalize dependent state0. generalize dependent addr0. *)
          remember from; induction action_trace'; subst; auto.
          specialize_hypotheses.
          intros deployed.
          destruct_action_chain_step.
          destruct_action_eval; rewrite_environment_equiv; subst; cbn in *.
          -
            specialize_hypotheses. destruct IHaction_trace' as (wc & deployed'). 
            exists wc. rewrite_environment_equiv. cbn; auto.
          - (* deployed *)
            destruct_address_eq.
            + exists wc. rewrite_environment_equiv; cbn. subst.
              rewrite address_eq_refl. auto.
            + specialize_hypotheses. destruct IHaction_trace' as (wc' & deployed'). 
              exists wc'. rewrite_environment_equiv. cbn.
              apply address_eq_ne' in n. rewrite n. auto.
          - (* call *)
            setoid_rewrite env_eq; cbn in *. 
            destruct_address_eq; now subst.
        }
        apply at_contract_states_deployed; auto.
      + (* invalid *)
        rewrite_environment_equiv. specialize_hypotheses. destruct IH as (wc & deployed).
        exists wc. rewrite_environment_equiv; auto. 
  Qed.

  (* If a state is reachable and contract state is stored on an address
    then that address must be a contract address *)
  Lemma contract_states_addr_format to (addr : Address) (state : SerializedValue) :
    reachable to ->
    env_contract_states to addr = Some state ->
    address_is_contract addr = true.
  Proof.
    intros ? deployed_state.
    apply contract_states_deployed in deployed_state as []; auto.
    now eapply contract_addr_format.
  Qed.

  Hint Resolve reachable_empty_state
              reachable_trans
              reachable_step : core.

  (* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
    from `mid` to `to`. This captures that there is a valid execution ending up in `to`
    and going through the state `mid` at some point *)
  Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

  (* A state is always reachable through itself *)
  Lemma reachable_through_refl : forall bstate,
    reachable bstate -> reachable_through bstate bstate.
  Proof.
    intros bstate reach.
    split; auto.
    do 2 constructor.
  Qed.

  (* Transitivity property of reachable_through and ChainStep *)
  Lemma reachable_through_trans' : forall from mid to,
    reachable_through from mid -> ChainStep mid to -> reachable_through from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  (* Transitivity property of reachable_through *)
  Lemma reachable_through_trans : forall from mid to,
    reachable_through from mid -> reachable_through mid to -> reachable_through from to.
  Proof.
    intros * [[trace_from] [trace_mid]] [_ [trace_to]].
    do 2 constructor.
    assumption.
    now eapply ChainedList.clist_app.
  Qed.

  (* Reachable_through can also be constructed from ChainStep instead of a
    ChainTrace since a ChainTrace can be constructed from a ChainStep *)
  Lemma reachable_through_step : forall from to,
    reachable from -> ChainStep from to -> reachable_through from to.
  Proof.
    intros * reach_from step.
    apply reachable_through_refl in reach_from.
    now eapply reachable_through_trans'.
  Qed.

  (* Any ChainState that is reachable through another ChainState is reachable *)
  Lemma reachable_through_reachable : forall from to,
    reachable_through from to -> reachable to.
  Proof.
    intros * [[trace_from] [trace_to]].
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  Hint Resolve reachable_through_refl
              reachable_through_trans'
              reachable_through_trans
              reachable_through_step
              reachable_through_reachable : core.

  (* If a state has a contract deployed to some addr then any other state
    reachable through the first state must also have the same contract
    deployed to the same addr *)
  Lemma reachable_through_contract_deployed : forall from to addr wc,
    reachable_through from to -> env_contracts from addr = Some wc ->
      env_contracts to addr = Some wc.
  Proof.
    intros * [reach [trace]] deployed.
    induction trace as [ | from mid to trace IH step ].
    - assumption.
    - destruct_chain_step.
      + rewrite_environment_equiv; cbn; destruct_address_eq; subst; easy.
      + specialize_hypotheses. 
        assert (at_reachable_through_contract_deployed :
          forall st,
            ActionChainTrace mid st ->
            env_contracts st addr = Some wc).
        {
          intros * trace'. 
          remember mid; induction trace'; subst; auto.
          specialize_hypotheses. destruct_action_chain_step.
          destruct_action_eval; rewrite_environment_equiv; subst; cbn in *; auto.
          destruct_address_eq; subst; easy.
        }
        apply at_reachable_through_contract_deployed; auto.
      + rewrite_environment_equiv; cbn; destruct_address_eq; subst; easy.
  Qed.

  (* If a state has a contract state on some addr then any other state
    reachable through the first state must also have the some contract
    state on the same addr *)
  Lemma reachable_through_contract_state : forall from to addr cstate,
    reachable_through from to -> env_contract_states from addr = Some cstate ->
      exists new_cstate, env_contract_states to addr = Some new_cstate.
  Proof.
    intros * [reachable [trace]] deployed_state.
    generalize dependent cstate.
    induction trace as [ | from mid to trace IH step ];
      intros cstate deployed_state.
    - now eexists.
    - destruct_chain_step.
      + setoid_rewrite env_eq; cbn; destruct_address_eq; subst; easy.
      + assert (at_reachable_through_contract_state :
          forall st,
            ActionChainTrace mid st ->
            exists new_cstate, env_contract_states st addr = Some new_cstate).
        {
          intros * trace'. 
          remember mid; induction trace'; subst.
          - apply (IH ltac:(auto) cstate ltac:(auto)).
          - specialize_hypotheses. destruct_action_chain_step.
            destruct_action_eval; setoid_rewrite env_eq; subst; cbn in *; auto
              ;destruct_address_eq; now subst.
        }
        apply at_reachable_through_contract_state; auto.
      + setoid_rewrite env_eq; cbn; destruct_address_eq; subst; easy.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower chain height *)
  Lemma reachable_through_chain_height : forall from to,
    reachable_through from to -> from.(chain_height) <= to.(chain_height).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step.
      + rewrite_environment_equiv; cbn; auto.
        now inversion valid_header.
      + assert (at_reachable_through_chain_height :
          forall st,
            ActionChainTrace mid st ->
            from.(chain_height) <= st.(chain_height)).
        {
          specialize_hypotheses. intros * trace'.
          remember mid; induction trace'; subst; auto.
          specialize_hypotheses.
          destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv;
            cbn; auto.
        }
        apply at_reachable_through_chain_height; auto.
      + rewrite_environment_equiv; cbn; auto.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower current slot *)
  Lemma reachable_through_current_slot : forall from to,
    reachable_through from to -> from.(current_slot) <= to.(current_slot).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step.
      + rewrite_environment_equiv; cbn; auto.
        now inversion valid_header.
      + assert (at_reachable_through_current_slot :
          forall st,
            ActionChainTrace mid st ->
            from.(current_slot) <= st.(current_slot)).
        {
          specialize_hypotheses. intros * trace'.
          remember mid; induction trace'; subst; auto.
          destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv;
            cbn; auto.
        }
        apply at_reachable_through_current_slot; auto.
      + rewrite_environment_equiv; cbn; auto.
  Qed.

  (* If a state is reachable through another state then it cannot have a lower finalized height *)
  Lemma reachable_through_finalized_height : forall from to,
    reachable_through from to -> from.(finalized_height) <= to.(finalized_height).
  Proof.
    intros * [reachable [trace]].
    induction trace as [ | from mid to trace IH step ].
    - apply Nat.le_refl.
    - destruct_chain_step.
      + rewrite_environment_equiv; cbn; auto.
        now inversion valid_header.
      + assert (at_reachable_through_finalized_height :
          forall st,
            ActionChainTrace mid st ->
            from.(finalized_height) <= st.(finalized_height)).
        {
          specialize_hypotheses. intros * trace'.
          remember mid; induction trace'; subst; auto.
          destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv;
            cbn; auto.
        }
        apply at_reachable_through_finalized_height; auto.
      + rewrite_environment_equiv; cbn; auto.
  Qed.

  (* Initial contract balance will always be positive in reachable states *)
  Lemma deployment_amount_nonnegative : forall {Setup : Type} `{Serializable Setup}
                                        bstate caddr dep_info
                                        (trace : ChainTrace empty_state bstate),
    deployment_info Setup trace caddr = Some dep_info ->
    (0 <= dep_info.(deployment_amount))%Z.
  Proof.
    intros * deployment_info_some.
    remember empty_state.
    induction trace; subst.
    - discriminate.
    - destruct_chain_step; auto.
      assert (at_deployment_amount_nonnegative :
        forall st
              (action_trace : ActionChainTrace mid st), 
          deployment_info_in_action_trace Setup trace action_trace caddr = Some dep_info ->
          (0 <= dep_info.(deployment_amount))%Z).
      {
        intros * deployment_info_some'.
        remember mid; induction action_trace0; subst; cbn in *; auto.
        specialize_hypotheses.
        destruct_action_chain_step.
        destruct_action_eval; auto.
        subst. unfold deployment_info_in_action_trace in *. cbn in *. 
        destruct_address_eq; auto. subst.
        destruct (deserialize setup).
        - inversion_subst deployment_info_some'. cbn. lia.
        - (* contra *)
          specialize (at_contract_not_disapear caddr mid mid0 action_trace0)
            as no_deployed_mid; auto. 
      }
      apply (at_deployment_amount_nonnegative to action_trace); auto.
  Qed.

  Definition receiver_can_receive_transfer (bstate : ChainState) act_body :=
    match act_body with
    | act_transfer to _ => address_is_contract to = false \/
      (exists wc state,
        env_contracts bstate to = Some wc /\
        env_contract_states bstate to = Some state /\
        forall (bstate_new : ChainState) ctx, exists new_state, wc_receive wc bstate_new ctx state None = Ok (new_state, [])) 
    | _ => True    
    end.

  
  (* This axiom states that for any reachable state and any contract it is
      decidable whether or not there is an address where the contract can be deployed to.
    This is not provable in general with the assumption ChainBase makes about
      addresses and the function address_is_contract. However, this should be
      provable in any sensible instance of ChainBase *)
  (* Axiom deployable_address_decidable : forall from bstate wc setup act_limit act_origin act_from amount,
    reachable_in_action_trace from bstate ->
    decidable (exists addr state, address_is_contract addr = true
              /\ env_contracts bstate addr = None
              /\ wc_init wc
                    (transfer_balance act_from addr amount bstate)
                    (build_ctx act_limit act_origin act_from addr amount amount)
                    setup = Ok state). *)

  Ltac action_not_decidable :=
    right; intro;
    match goal with
    | H : exists bstate new_acts, inhabited (ActionEvaluation _ _ bstate new_acts) |- False =>
      destruct H as [bstate_new [new_acts [action_evaluation]]];
      destruct_action_eval; try congruence
    end; repeat
    match goal with
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} = {| act_limit := _; act_origin := _; act_from := _; act_body := match ?msg with | Some _ => _ | None =>_ end |} |- False =>
      destruct msg
    | H : {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} = {| act_limit := _; act_origin := _; act_from := _; act_body := _ |} |- False =>
      inversion H; subst; clear H
    end.

  Ltac action_decidable :=
    left; do 2 eexists; constructor;
    match goal with
    | H : wc_receive _ _ _ _ ?m = Ok _ |- _ => eapply (eval_call _ _ _ _ _ _ m)
    | H : wc_init _ _ _ _ = Ok _ |- _ => eapply eval_deploy
    | H : context [act_transfer _ _] |- _ => eapply eval_transfer
    end;
    eauto; try now constructor.

  Ltac rewrite_balance :=
    match goal with
    | H := context [if (_ =? ?to)%address then _ else _],
      H2 : Environment |- _ =>
      assert (new_to_balance_eq : env_account_balances H2 to = H);
      [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
      now rewrite <- new_to_balance_eq in *]
    end.

  (* For any reachable state and an action it is decidable if it is
      possible to evaluate the action in the state *)
  (* extend to refer for a state in ActionChainTrace *)
  Open Scope Z_scope.

  Lemma action_evaluation_decidable : forall from bstate act,
    reachable_in_action_trace from bstate ->
    decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
  Proof.
    intros * reach.
    destruct act eqn:Hact.
    destruct act_body;
      (destruct (amount >=? 0) eqn:amount_positive;
      [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
        action_not_decidable; now rewrite Z.geb_leb, Z.leb_gt in amount_positive (* Eliminate cases where amount is negative *)];
      [| action_not_decidable; now rewrite Z.leb_gt in balance ]); (* Eliminate cases where sender does not have enough balance *)
    try (destruct (address_is_contract to) eqn:to_is_contract;
      [destruct (env_contracts bstate to) eqn:to_contract;
      [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
    try now action_not_decidable. (* Eliminate cases with obvious contradictions *)
    all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
    all : rewrite Z.leb_le in balance.
    - (* act_body = act_transfer to amount *)
      pose (new_to_balance := if (address_eqb act_from to)
                          then (env_account_balances bstate to)
                          else (env_account_balances bstate to) + amount).
      destruct (wc_receive w
          (transfer_balance act_from to amount bstate)
          (build_ctx act_limit act_origin act_from to new_to_balance amount)
          s None) eqn:receive.
      + (* Case: act_transfer is evaluable by eval_call *)
        destruct t.
        pose (bstate' := (set_contract_state to s0
                        (transfer_balance act_from to amount bstate))).
        destruct (Nat.ltb_spec 0 act_limit)%nat.
        * action_decidable. 
          rewrite_balance.
        * (* fail for act_limit *)
          action_not_decidable; lia.
      + (* Case: act_transfer is not evaluable by eval_call
            because wc_receive returned None *)
        action_not_decidable.
        rewrite_balance.
    - (* act_body = act_transfer to amount *)
      (* Case: act_transfer is evaluable by eval_transfer *)
      pose (bstate' := (transfer_balance act_from to amount bstate)).
      destruct (Nat.ltb_spec 0 act_limit)%nat.
      + action_decidable.
      + action_not_decidable; lia.
    - (* act_body = act_call to amount msg *)
      pose (new_to_balance := if (address_eqb act_from to)
                          then (env_account_balances bstate to)
                          else (env_account_balances bstate to) + amount).
      destruct (wc_receive w
          (transfer_balance act_from to amount bstate)
          (build_ctx act_limit act_origin act_from to new_to_balance amount)
          s (Some msg)) eqn:receive.
      + (* Case: act_call is evaluable by eval_call *)
        destruct t.
        pose (bstate' := (set_contract_state to s0
                        (transfer_balance act_from to amount bstate))).
        destruct (Nat.ltb_spec 0 act_limit)%nat.
        * action_decidable. rewrite_balance.
        * action_not_decidable; lia.        
      + (* Case: act_call is not evaluable by eval_call
            because wc_receive returned None *)
        action_not_decidable.
        rewrite_balance.
    - (* act_body = act_call to amount msg *)
      (* Case: contradiction *)
      action_not_decidable.
      now apply (contract_addr_format_in_action_trace to_addr wc reach) in deployed; auto.
    - (* act_body = act_deploy amount c setup *)
      apply deployable_address_decidable
        with (wc := c) (setup := setup) (act_limit := act_limit) (act_origin := act_origin)
        (act_from := act_from) (amount := amount)
        in reach.
      destruct reach as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
      + (* Case: act_deploy is evaluable by eval_deploy *)
        pose (bstate' := (set_contract_state to state
                        (add_contract to c
                        (transfer_balance act_from to amount bstate)))).
        destruct (Nat.ltb_spec 0 act_limit)%nat.
        * action_decidable. 
        * action_not_decidable; lia.                             
      + (* Case: act_deploy is not evaluable by eval_deploy
            because no there is no available contract address
            that this contract can be deployed to *)
        action_not_decidable.
        apply no_deployable_addr.
        eauto.
  Qed.
  Close Scope Z_scope.

  


  Hint Resolve reachable_in_action_trace_refl
             reachable_in_action_trace_trans
             reachable_in_action_trace_step : core.

  Lemma empty_queue : forall bstate (P : ChainState -> Prop),
    reachable bstate ->
    P bstate ->
    (forall (from bstate bstate' : ChainState) act acts new_acts, 
      reachable_in_action_trace from bstate -> 
      P bstate ->
      chain_state_queue bstate = act :: acts -> 
      chain_state_queue bstate' = new_acts ++ acts ->
      (inhabited (ActionEvaluation bstate act bstate' new_acts) \/ EnvironmentEquiv from bstate') -> 
      P bstate') 
        ->
    exists bstate', 
      reachable_through bstate bstate' /\ 
      P bstate' /\ 
      (chain_state_queue bstate') = [].
  Proof.
    intros * reach.
    remember (chain_state_queue bstate) as queue.
    generalize dependent bstate.
    induction queue; intros bstate reach Hqueue_eq HP HP_preserved.
    - (* Case: queue is already empty, thus we are already done *)
      now eexists.
    - (* Case: queue contains at least one action,
          thus we need to either discard or evaluate it *)
      specialize (queue_from_account bstate reach) as acts_from_account. 
      rewrite <- Hqueue_eq in acts_from_account.
      apply list.Forall_cons_1 in acts_from_account as [act_from_a acts_from_account].
      specialize (chain_step_serial bstate reach) as (bstate' & [step]).
      assert (reach' : reachable bstate') by apply (reachable_step bstate bstate' reach step).
      specialize (IHqueue bstate' ltac:(auto)).
      destruct_chain_step; try congruence.
      + (* Case: the action finish *)
        rewrite queue_prev in *. inversion_subst Hqueue_eq.
        destruct (IHqueue) as (empty_state & reach_empty & HP_empty & queue_empty); auto.
        {
          assert (HP_preserved_action_trace : 
            forall st, ActionChainTrace bstate st ->
              P st).
          {
            intros * trace'. remember bstate; induction trace'; subst; auto.
            destruct_action_chain_step.
            specialize (HP_preserved bstate mid to act0 acts new_acts). specialize_hypotheses.
            assert (reach_th_bstate : reachable_in_action_trace bstate bstate).
            { unfold reachable_in_action_trace. split; auto. repeat constructor. }
            assert (reach_mid : reachable_in_action_trace bstate mid).
            { apply (reachable_in_action_trace_trans reach_th_bstate trace'). }
            specialize_hypotheses. auto.   
          }
          apply HP_preserved_action_trace; auto.
        }
        exists empty_state. split; auto. 
        assert (step : ChainStep bstate bstate') by (eapply step_action; eauto).
        eapply reachable_through_trans; eauto.
      + (* Case: the action cannnot finish *)
        rewrite queue_prev in *. inversion_subst Hqueue_eq.
        destruct (IHqueue) as (empty_state & reach_empty & HP_empty & queue_empty); auto.        
        {
          specialize (HP_preserved bstate bstate bstate' act (chain_state_queue bstate') []
            ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
          apply HP_preserved. right. rewrite_environment_equiv. reflexivity.
        }
        exists empty_state. split; auto.
        assert (step : ChainStep bstate bstate') by (eapply step_action_invalid; eauto).
        eapply reachable_through_trans; eauto.
  Qed.

  (* wc_receive and contract receive are equivalent *)
  
  Lemma wc_receive_to_receive : forall {Setup Msg State Error : Type}
                                      `{Serializable Setup}
                                      `{Serializable Msg}
                                      `{Serializable State}
                                      `{Serializable Error}
                                      (contract : Contract Setup Msg State Error)
                                      chain cctx cstate msg new_cstate new_acts,
    contract.(receive) chain cctx cstate (Some msg) = Ok (new_cstate, new_acts) <->
    wc_receive contract chain cctx ((@serialize State _) cstate) (Some ((@serialize Msg _) msg)) = Ok ((@serialize State _) new_cstate, new_acts).
  Proof.
    split; intros receive_some.
    - cbn.
      rewrite !deserialize_serialize.
      cbn.
      now rewrite receive_some.
    - apply wc_receive_strong in receive_some as
        (prev_state' & msg' & new_state' & prev_state_eq & msg_eq & new_state_eq & receive_some).
      apply serialize_injective in new_state_eq. subst.
      rewrite deserialize_serialize in prev_state_eq.
      inversion prev_state_eq. subst.
      destruct msg' eqn:Hmsg.
      + cbn in msg_eq.
        now rewrite deserialize_serialize in msg_eq.
      + inversion msg_eq.
  Qed.

  (* wc_init and contract init are equivalent *)
  Lemma wc_init_to_init : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                chain cctx cstate setup,
    contract.(init) chain cctx setup = Ok cstate <->
    wc_init contract chain cctx ((@serialize Setup _) setup) = Ok ((@serialize State _) cstate).
  Proof.
    split; intros init_some.
    - cbn.
      rewrite deserialize_serialize.
      cbn.
      now rewrite init_some.
    - apply wc_init_strong in init_some as
        (setup_strong & result_strong & serialize_setup & serialize_result & init_some).
      apply serialize_injective in serialize_result. subst.
      rewrite deserialize_serialize in serialize_setup.
      now inversion serialize_setup.
  Qed.

  Open Scope Z_scope.
  (* Lemma showing that there exists a future ChainState with an added block *)
  Lemma add_block : forall bstate reward creator acts slot_incr,
    reachable bstate ->
    chain_state_queue bstate = [] ->
    address_is_contract creator = false ->
    reward >= 0 ->
    (slot_incr > 0)%nat ->
    Forall act_is_from_account acts ->
    Forall act_origin_is_eq_from acts ->
      (exists bstate',
        reachable_through bstate bstate'
      /\ chain_state_queue bstate' = acts
      /\ EnvironmentEquiv
          bstate'
          (add_new_block_to_env {| block_height := S (chain_height bstate);
            block_slot := current_slot bstate + slot_incr;
            block_finalized_height := finalized_height bstate;                     
            block_creator := creator;
            block_reward := reward; |} bstate)).
  Proof.
    intros * reach queue creator_not_contract
      reward_positive slot_incr_positive
      acts_from_accounts origins_from_accounts.
    pose (header :=
      {| block_height := S (chain_height bstate);
        block_slot := current_slot bstate + slot_incr;
        block_finalized_height := finalized_height bstate;
        block_creator := creator;
        block_reward := reward; |}).
    pose (bstate_with_acts := (bstate<|chain_state_queue := acts|>
                                    <|chain_state_env := add_new_block_to_env header bstate|>)).
    assert (step_with_acts : ChainStep bstate bstate_with_acts).
    { eapply step_block; try easy.
      - constructor; try easy.
        + cbn. lia.
        + split; try (cbn; lia). cbn.
          now apply finalized_heigh_chain_height.
    }
    exists bstate_with_acts.
    split. eapply reachable_through_step; eauto.
    split; eauto.
    constructor; try reflexivity.
  Qed.

  (* Lemma showing that there exists a future ChainState with the
      same contract states where the current slot is <slot> *)
  Lemma forward_time_exact : forall bstate reward creator slot,
    reachable bstate ->
    chain_state_queue bstate = [] ->
    address_is_contract creator = false ->
    reward >= 0 ->
    (current_slot bstate < slot)%nat ->
      (exists bstate' header,
        reachable_through bstate bstate'
      /\ IsValidNextBlock header bstate
      /\ (slot = current_slot bstate')%nat
      /\ chain_state_queue bstate' = []
      /\ EnvironmentEquiv
          bstate'
          (add_new_block_to_env header bstate)).
  Proof.
    intros bstate reward creator slot reach queue
      creator_not_contract reward_positive slot_not_hit.
    eapply add_block with (slot_incr := (slot - current_slot bstate)%nat) in reach as new_block; try easy.
    destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
    do 2 eexists.
    split; eauto.
    do 3 try split; only 9: apply env_eq; eauto; cbn; try lia.
    - now apply finalized_heigh_chain_height.
    - rewrite_environment_equiv. cbn. lia.
  Qed.

  (* Lemma showing that there exists a future ChainState with the
    same contract states where the current slot is at least <slot> *)
  Lemma forward_time : forall bstate reward creator slot,
    reachable bstate ->
    chain_state_queue bstate = [] ->
    address_is_contract creator = false ->
    reward >= 0 ->
      (exists bstate' header,
        reachable_through bstate bstate'
      /\ IsValidNextBlock header bstate
      /\ (slot <= current_slot bstate')%nat  
      /\ chain_state_queue bstate' = []
      /\ EnvironmentEquiv
          bstate'
          (add_new_block_to_env header bstate)).
  Proof.
    intros * reach queue creator_not_contract reward_positive.
    destruct (slot - current_slot bstate)%nat eqn:slot_hit.
    - eapply add_block with (slot_incr := 1%nat) in reach as new_block; try easy.
      destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
      do 2 eexists.
      split; eauto.
      do 3 try split; only 9: apply env_eq; eauto; cbn; try lia.
      + now apply finalized_heigh_chain_height.
      + apply NPeano.Nat.sub_0_le in slot_hit.
        rewrite_environment_equiv. cbn. lia.
    - specialize (forward_time_exact bstate reward creator slot) as
        (bstate' & header & reach' & header_valid & slot_hit' & queue' & env_eq); eauto.
      lia.
      do 2 eexists.
      destruct_and_split; eauto.
      lia.
  Qed.

  (* Lemma showing that there exists a future ChainState
      where the contract call is evaluated *)
  Lemma evaluate_action : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                from_bstate bstate limit origin from caddr amount msg acts new_acts
                                cstate new_cstate,
    reachable_in_action_trace from_bstate bstate ->
    chain_state_queue bstate = {| act_limit := limit;
                                  act_from := from;
                                  act_origin := origin;
                                  act_body := act_call caddr amount ((@serialize Msg _) msg) |} :: acts ->
    (0 < limit)%nat ->
    (amount >= 0) ->
    env_account_balances bstate from >= amount ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    env_contract_states bstate caddr = Some ((@serialize State _) cstate) ->
    Blockchain_modify_2.receive contract (transfer_balance from caddr amount bstate)
                      (build_ctx limit origin from caddr (if (address_eqb from caddr)
                          then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount) amount)
                      cstate (Some msg) = Ok (new_cstate, new_acts) ->
      (exists bstate',
        reachable_in_action_trace from_bstate bstate'
      /\ env_contract_states bstate' caddr = Some ((@serialize State _) new_cstate)
      /\ chain_state_queue bstate' = (map (build_act (limit - 1) origin caddr) new_acts) ++ acts
      /\ EnvironmentEquiv
          bstate'
          (set_contract_state caddr ((@serialize State _) new_cstate) (transfer_balance from caddr amount bstate))).
  Proof.
    intros * reach queue enough_limit amount_nonnegative enough_balance%Z.ge_le
      deployed deployed_state receive_some.
    pose (new_to_balance := if (address_eqb from caddr)
                          then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount).
    pose (bstate' := (bstate<|chain_state_queue := (map (build_act (limit - 1) origin caddr) new_acts) ++ acts|>
                            <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                    (transfer_balance from caddr amount bstate)|>)).
    assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance) by
    (cbn; destruct_address_eq; easy).
    assert (step : ActionChainStep bstate bstate').
    - eapply action_step_action; eauto.
      eapply eval_call with (msg := Some ((@serialize Msg _) msg)); eauto.
      + rewrite new_to_balance_eq.
        now apply wc_receive_to_receive in receive_some.
      + constructor; reflexivity.
    - exists bstate'.
      split. apply (reachable_in_action_trace_step reach step).
      split; eauto. subst bstate'. cbn. rewrite address_eq_refl. auto.
      repeat split; eauto.
  Qed.

  (* Lemma showing that there exists a future ChainState
      where the transfer action is evaluated *)
  Lemma evaluate_transfer : forall from_bstate bstate limit origin from to amount acts,
    reachable_in_action_trace from_bstate bstate ->
    chain_state_queue bstate = {| act_limit := limit;
                                  act_from := from;
                                  act_origin := origin;
                                  act_body := act_transfer to amount |} :: acts ->
    (0 < limit)%nat ->
    amount >= 0 ->
    env_account_balances bstate from >= amount ->
    address_is_contract to = false ->
      (exists bstate',
        reachable_in_action_trace from_bstate bstate'
      /\ chain_state_queue bstate' = acts
      /\ EnvironmentEquiv
          bstate'
          (transfer_balance from to amount bstate)).
  Proof.
    intros * reach queue enough_limit amount_nonnegative enough_balance%Z.ge_le to_not_contract.
    pose (bstate' := (bstate<|chain_state_queue := acts|>
                            <|chain_state_env := (transfer_balance from to amount bstate)|>)).
    assert (step : ActionChainStep bstate bstate').
    - eapply action_step_action with (new_acts := []); eauto.
      eapply eval_transfer; eauto.
      constructor; reflexivity.
    - eexists bstate'.
      split; eauto.
      repeat split; eauto.
  Qed.

Local Lemma list_app_nil {T : Type} {l1 l2 : list T} :
  l2 = l1 ++ l2 -> l1 = [].
Proof.
    replace (l2 = l1 ++ l2) with (rev (rev l2) = rev ( rev (l1 ++ l2))). 2: repeat rewrite List.rev_involutive; auto.
    assert (rev_injective : forall {T: Type} (l1 l2: list T), rev l1 = rev l2 -> l1 = l2).
    {
      intros *. intro H.
      rewrite <- rev_involutive.
      rewrite <- H.
      rewrite -> rev_involutive.
      reflexivity.
    }
    intros. apply rev_injective in H. rewrite rev_app_distr in H.
    induction (rev l2); auto. cbn in *. inversion H. auto.
Qed.

Local Ltac solve_list_contra :=
  match goal with
  | [H: ?l = ?x :: ?l |- _] => apply list_cons_not in H; auto
  | [H: ?x :: ?l = ?l |- _] => apply eq_sym in H; apply list_cons_not in H; auto
  | [H: ?l = ?x :: ?l' ++ ?l |- _] => 
      rewrite app_comm_cons in H; apply list_app_nil in H; discriminate H
  | [H: ?x :: ?l' ++ ?l = ?l |- _] => 
      apply eq_sym in H;
      rewrite app_comm_cons in H; apply list_app_nil in H; discriminate H
  | [H: ?l = (?x :: ?l') ++ ?l |- _] => apply list_app_nil in H; discriminate H
  | [H: (?x :: ?l') ++ ?l = ?l |- _] => apply eq_sym in H; apply list_app_nil in H; discriminate H
  end.


Local Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

  (* Lemma showing that if an action in the queue is invalid then
      there exists a future ChainState with the same environment
      where that action is discarded *)
  Lemma discard_invalid_action : forall from_bstate bstate act act' acts acts',
    reachable_in_action_trace from_bstate bstate ->
    chain_state_queue from_bstate = act :: acts ->
    bstate.(chain_state_queue) = act' :: acts' ++ acts ->
    (forall (bstate0 : Environment) (new_acts : list Action), ActionEvaluation bstate act' bstate0 new_acts -> False) ->
      (exists from_bstate',
        reachable_through from_bstate from_bstate'
      /\ chain_state_queue from_bstate' = acts
      /\ EnvironmentEquiv from_bstate' from_bstate).
  Proof.
    intros * (reach & [action_trace]) queue queue_bstate no_action_evaluation.
    
    specialize (action_finish_decidable from_bstate act acts reach ltac:(auto)) 
      as [(finish_bstate & queue_finish & [trace_finish])
          | no_finish].
    - (* contra *)
      specialize (action_trace_no_branch action_trace trace_finish ltac:(auto))
        as [(finish_bstate' & trace_finish' & env_eq_finish & queue_eq_finish)
            | (bstate' & trace_bstate' & env_eq_bstate & queue_eq_bstate)].
      + (* bstate -> finish' *)
        specialize (action_trace_step trace_finish') 
          as [|(next & [step_next] & [trace_next])]; subst. 
        { rewrite queue_eq_finish in *. solve_list_contra. }
        destruct_action_chain_step. rewrite queue_prev in *.  inversion_subst queue_bstate.
        edestruct no_action_evaluation; eauto. 
      + (* finish -> bstate' *) 
        assert (reach_finish : reachable_in_action_trace from_bstate finish_bstate).
        { unfold reachable_in_action_trace. split; auto. }
        destruct (action_trace_step trace_bstate')
          as [|(next & [step_next] & [trace_next])]; subst.
        * rewrite queue_eq_bstate in *. solve_list_contra.
        * assert (reach_next : reachable_in_action_trace from_bstate next).
          apply (reachable_in_action_trace_step reach_finish step_next).
          destruct_action_chain_step.
          specialize (action_trace_drop_le reach_next trace_next) as Hle.
          specialize (queue_from_account from_bstate reach) as from_accs.
          specialize (emited_acts_from_is_always_contract reach_finish queue_prev eval) as from_contracts.
          rewrite_queue. apply Forall_cons_iff in from_accs as (from_acc & from_accs).
          rewrite drop_from_contract in Hle; auto. rewrite app_comm_cons in Hle.
          assert (Hle' : (length (list_drop_contract_action (act0 :: acts)) <= 
            length (list_drop_contract_action ((act' :: acts') ++ act0 :: acts)))%nat).
          { unfold list_drop_contract_action. apply list_drop_app_le. }    
          assert (Hle'' : (length (list_drop_contract_action (act0 :: acts)) 
            <= length (list_drop_contract_action acts))%nat) by lia.
          rewrite no_drop_from_account in Hle''; auto. 
          apply Forall_cons_iff in from_accs as (_ & from_accs).
          rewrite no_drop_from_account in Hle''; auto. cbn in *. lia. 
    - (* step_action_invalid *)
      pose (next := (from_bstate<|chain_state_queue := acts|>)).
      assert (ChainStep from_bstate next).
      {
        eapply step_action_invalid; eauto. subst next. cbn. reflexivity.
        intros. eapply no_finish. split; eauto.
      }
      eexists next. repeat (split; auto). 
  Qed.

  (* Lemma showing that there exists a future ChainState
    where the contract is deployed *)
  Lemma deploy_contract : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                from_bstate bstate limit origin from caddr amount acts setup cstate,
    reachable_in_action_trace from_bstate bstate ->
    chain_state_queue bstate = {| act_limit := limit;
                                  act_from := from;
                                  act_origin := origin;
                                  act_body := act_deploy amount contract ((@serialize Setup _) setup) |} :: acts ->
    (0 < limit)%nat ->
    amount >= 0 ->
    env_account_balances bstate from >= amount ->
    address_is_contract caddr = true ->
    env_contracts bstate caddr = None ->
    Blockchain_modify_2.init contract
          (transfer_balance from caddr amount bstate)
          (build_ctx limit origin from caddr amount amount)
          setup = Ok cstate ->
      (exists bstate' (action_trace : ActionChainTrace from_bstate bstate'),
        reachable_in_action_trace from_bstate bstate'
      /\ env_contracts bstate' caddr = Some (contract : WeakContract)
      /\ env_contract_states bstate' caddr = Some ((@serialize State _) cstate)
      /\ act_trace_deployment_info Setup action_trace caddr = Some (build_deployment_info origin from amount setup)
      /\ chain_state_queue bstate' = acts
      /\ EnvironmentEquiv
          bstate'
          (set_contract_state caddr ((@serialize State _) cstate)
          (add_contract caddr contract
          (transfer_balance from caddr amount bstate)))).
  Proof.
    intros * reach queue enough_limit amount_nonnegative enough_balance%Z.ge_le
      caddr_is_contract not_deployed init_some.
    pose (bstate' := (bstate<|chain_state_queue := acts|>
                            <|chain_state_env :=
                              (set_contract_state caddr ((@serialize State _) cstate)
                              (add_contract caddr contract
                              (transfer_balance from caddr amount bstate)))|>)).
    assert (step : ActionChainStep bstate bstate').
    - eapply action_step_action with (new_acts := []); eauto.
      eapply eval_deploy; eauto; try lia.
      + now apply wc_init_to_init in init_some.
      + constructor; reflexivity.
    - exists bstate'.
      destruct reach as ([trace] & [action_trace_bstate]).
      pose (ChainedList.snoc action_trace_bstate step) as action_trace_bstate'.
      exists action_trace_bstate'.
      split.
      { unfold reachable_in_action_trace. split. unfold reachable. all: constructor; auto. }
      repeat split; eauto;
      try (cbn; now destruct_address_eq).
      cbn. destruct_action_chain_step. 
      destruct_action_eval; rewrite_queue; cbn in *; subst; cbn in *; try congruence.
      * (* deploy *)
        destruct_address_eq.
        -- inversion_subst queue. 
          now rewrite deserialize_serialize.
        -- inversion env_eq.
          cbn in contracts_eq.
          specialize (contracts_eq caddr).
          now rewrite address_eq_refl, address_eq_ne in contracts_eq.
      * now destruct msg.
  Qed.

  Lemma step_reachable_through_exists : forall from mid (P : ChainState -> Prop),
    reachable_through from mid ->
    (exists to : ChainState, reachable_through mid to /\ P to) ->
    (exists to : ChainState, reachable_through from to /\ P to).
  Proof.
    intros * reach [to [reach_ HP]].
    now exists to.
  Qed.

  Lemma wc_receive_to_receive' : forall {Setup Msg State Error : Type}
                                    `{Serializable Setup}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                    `{Serializable Error}
                                    (contract : Contract Setup Msg State Error)
                                    chain cctx cstate msg new_cstate new_acts s,
  deserialize s = Some cstate ->
  contract.(receive) chain cctx cstate (Some msg) = Ok (new_cstate, new_acts) <->
    wc_receive contract chain cctx s (Some ((@serialize Msg _) msg)) = Ok ((@serialize State _) new_cstate, new_acts).
  Proof.
    intros * deser_some. split.
    - cbn. intro receive_some. rewrite deser_some, deserialize_serialize; cbn. 
      rewrite receive_some. cbn. auto.
    - intros wc_receive_some.
      apply wc_receive_strong in wc_receive_some as
        (prev_state' & msg' & new_state' & prev_state_eq & msg_eq & new_state_eq & receive_some).
      apply serialize_injective in new_state_eq. subst.
      rewrite deser_some in *. inversion_subst prev_state_eq.
      destruct msg' eqn:Hmsg.
      + cbn in msg_eq.
        now rewrite deserialize_serialize in msg_eq.
      + inversion msg_eq.
  Qed. 

    
  Lemma evaluate_action' : forall {Setup Msg State Error : Type}
                                `{Serializable Setup}
                                `{Serializable Msg}
                                `{Serializable State}
                                `{Serializable Error}
                                (contract : Contract Setup Msg State Error)
                                from_bstate bstate limit origin from caddr amount msg acts new_acts
                                (cstate new_cstate : State),
    reachable_in_action_trace from_bstate bstate ->
    chain_state_queue bstate = {| act_limit := limit;
                                  act_from := from;
                                  act_origin := origin;
                                  act_body := act_call caddr amount ((@serialize Msg _) msg) |} :: acts ->
    (0 < limit)%nat ->
    (amount >= 0)%Z ->
    (env_account_balances bstate from >= amount)%Z ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate -> 
    Blockchain_modify_2.receive contract (transfer_balance from caddr amount bstate)
                      (build_ctx limit origin from caddr (if (address_eqb from caddr)
                          then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount) amount)
                      cstate (Some msg) = Ok (new_cstate, new_acts) ->
      (exists bstate',
        reachable_in_action_trace from_bstate bstate'
      /\ contract_state bstate' caddr = Some new_cstate
      /\ chain_state_queue bstate' = (List.map (build_act (limit - 1) origin caddr) new_acts) ++ acts
      /\ EnvironmentEquiv
          bstate'
          (set_contract_state caddr (serialize new_cstate) (transfer_balance from caddr amount bstate))).
  Proof.
    intros * reach queue enough_limit amount_nonnegative enough_balance%Z.ge_le
      deployed deployed_state receive_some.
    pose (new_to_balance := if (address_eqb from caddr)
                          then (env_account_balances bstate caddr)
                          else (env_account_balances bstate caddr) + amount).
    pose (bstate' := (bstate<|chain_state_queue := (map (build_act (limit - 1) origin caddr) new_acts) ++ acts|>
                            <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                    (transfer_balance from caddr amount bstate)|>)).
    assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance) by
    (cbn; destruct_address_eq; easy).
    assert (step : ActionChainStep bstate bstate').
    - eapply action_step_action; eauto.
      cbn in deployed_state.
      destruct (env_contract_states bstate caddr) eqn:Hstate; try congruence.
      eapply eval_call with (msg := Some ((@serialize Msg _) msg))
        (prev_state := s); eauto. 
      + apply wc_receive_to_receive' with (cstate := cstate); auto.
        rewrite new_to_balance_eq. 
        apply receive_some.
      + constructor; reflexivity.
    - exists bstate'. 
      split. apply (reachable_in_action_trace_step reach step).
      subst bstate'. cbn.
      split; eauto. rewrite address_eq_refl. rewrite deserialize_serialize. auto.
      repeat split; eauto.
  Qed.
  Close Scope Z_scope.

End BuildUtils.


Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Global Hint Resolve reachable_in_action_trace_refl
            reachable_in_action_trace_trans
            reachable_in_action_trace_step : core.

Local Ltac update_fix term1 term2 H H_orig H' :=
  match H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H_orig H'
  | _ =>
    let h := fresh "H" in
      assert H; [H' | clear H_orig; rename h into H_orig]
  end.

(* Replaces all occurrences of <term1> with <term2> in hypothesis <H>
    using tactic <H'> to prove the old hypothesis implies the updated *)
Local Ltac update_ term1 term2 H H' :=
  match type of H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H H'
  end.

Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) := update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) "by" tactic(G) := update_ t1 t2 H G.
Tactic Notation "update" constr(t2) "in" hyp(H) := let t1 := type of H in update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t2) "in" hyp(H) "by" tactic(G) := let t1 := type of H in update_ t1 t2 H G.

Local Ltac only_on_match tac :=
  match goal with
  | |- exists bstate', reachable_through ?bstate bstate' /\ _ => tac
  | |- _ => idtac
  end.

Local Ltac update_chainstate bstate1 bstate2 :=
  match goal with
  | H : reachable bstate1 |- _ => clear H
  | H : chain_state_queue bstate1 = _ |- _ => clear H
  | H : IsValidNextBlock _ bstate1.(chain_state_env).(env_chain) |- _ => clear H
  | H : reachable_through bstate1 bstate2 |- _ =>
      update (reachable bstate2) in H
  | H : env_contracts bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : env_contract_states bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : context [ bstate1 ] |- _ =>
    match type of H with
    | EnvironmentEquiv _ _ => fail 1
    | _ => update bstate1 with bstate2 in H by (try (rewrite_environment_equiv; cbn; easy))
    end
  end;
  only_on_match ltac:(progress update_chainstate bstate1 bstate2).

(* Tactic for updating goal and all occurrences of an old ChainState
    after adding a future ChainState to the environment. *)
Ltac update_all :=
  match goal with
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) (add_new_block_to_env ?header ?bstate1.(chain_state_env)) |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        (try clear dependent header);
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) _ |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2 |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update (reachable bstate2) in Hreach;
      only_on_match ltac:(clear dependent bstate1)
  end.

Ltac forward_time slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct (forward_time bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac forward_time_exact slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct (forward_time_exact bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac add_block acts_ slot_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct add_block with (acts := acts_) (slot_incr := slot_)
        as [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | apply Hqueue| | | | | |]
  end.

Ltac evaluate_action contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct (evaluate_action contract_) as
        [new_bstate [new_reach [new_deployed_state [new_queue new_env_eq]]]];
      [apply Hreach | rewrite Hqueue | | | | | | ]
  end.

Ltac evaluate_transfer :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct evaluate_transfer as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | | ]
  end.

Ltac discard_invalid_action :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct discard_invalid_action as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | ]
  end.

Ltac empty_queue H :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let temp_H := fresh "H" in
  let temp_eval := fresh "eval" in
   match goal with
  | Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      pattern (bstate) in H;
      match type of H with
      | ?f bstate =>
        edestruct (empty_queue bstate f) as
          [new_bstate [new_reach [temp_H new_queue]]];
        [apply Hreach | apply H |
        clear H;
        intros ?bstate_from ?bstate_to ?act ?acts ?reach_from ?reach_to
          H ?queue_from ?queue_to [[temp_eval] | ?env_eq];
          only 1: destruct_action_eval |
        clear H; rename temp_H into H]
      end
  end.

Ltac deploy_contract contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_contract_deployed := fresh "contract_deployed" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_cstate := fresh "cstate" in
  let contract_not_deployed := fresh "trace" in
  let deploy_info := fresh "deploy_info" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate,
    Haddress : address_is_contract ?caddr = true,
    Hdeployed : env_contracts ?bstate.(chain_state_env) ?caddr = None |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      edestruct (deploy_contract contract_) as
        (new_bstate & trace & new_reach & new_contract_deployed &
          new_deployed_state & deploy_info & new_queue & new_env_eq);
      [apply Hreach | rewrite Hqueue | | |
       apply Haddress | apply Hdeployed | |
       clear Haddress Hdeployed;
       match type of new_deployed_state with
       | env_contract_states _ _ = Some ((@serialize _ _) ?state) => remember state as new_cstate
       end
       ]
  end.