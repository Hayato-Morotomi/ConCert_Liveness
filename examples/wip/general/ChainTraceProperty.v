From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Logic.Decidable.
From Coq Require Import ZArith.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Monad.
From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import ContractCommon_modify.

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

Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

  Ltac reach_induction :=
  match goal with
  | trace : ChainTrace empty_state ?bstate |- _ =>
    cbn;
    remember empty_state;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = empty_state |- _ => subst x
    end;
    [try discriminate |
    destruct_chain_step; try destruct_action_eval;
    match goal with
    | env_eq : EnvironmentEquiv _ _ |- _ =>
        try rewrite env_eq in *; try setoid_rewrite env_eq
    end;
    repeat (specialize (IH ltac:(auto)))]; auto
  end.


  Ltac trace_induction :=
  match goal with
  | trace : ChainTrace ?from ?to |- _ =>
    cbn;
    remember from;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = from |- _ => subst x
    end;
    [try discriminate |
    destruct_chain_step;
    repeat (specialize (IH ltac:(auto)))]; auto
  end.

  Ltac action_trace_induction :=
  match goal with
  | trace : ActionChainTrace ?from ?to |- _ =>
    cbn;
    remember from;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = from |- _ => subst x
    end;
    [try discriminate |
    destruct_action_chain_step;
    repeat (specialize (IH ltac:(auto)))]; auto
  end.

  Ltac action_trace_induction_intermidiate :=
    match goal with
    | H : ActionChainTrace ?mid ?to |- _ =>
        pattern to;
        match goal with
        | |- ?P to =>
            let A := fresh "A" in
            enough (forall st, ActionChainTrace mid st -> P st) as A;
            [ 
              cbn in *; eapply A; eauto
            | 
            ];
            let action_trace := fresh "action_trace" in
            let IH := fresh "IH" in
            intros ?st action_trace;
            remember mid;
            induction action_trace as [| * IH ?step];
            match goal with
            | H : ?x = mid |- _ => subst x
            end;
            [
            | destruct_action_chain_step;
            repeat (specialize (IH ltac:(auto)))]; auto
        end
    end.

Section ChainTraceProperty.
  Context {Base : ChainBase}.

  Lemma trace_step {from mid to} :
    ChainStep from mid ->
    ChainTrace mid to ->
    inhabited (ChainTrace from to).
  Proof.
    intros step trace.
    generalize dependent step. generalize dependent from.
    induction trace.
    - intros * step. constructor. eapply snoc; eauto. apply clnil.
    - intros * step. 
      destruct (IHtrace from0); auto.
      constructor; eapply snoc; eauto.
  Qed. 

  Definition act_is_from_contract (act : Action) : Prop :=
    address_is_contract (act_from act) = true.

  Lemma act_from_acc_or_contract act :
    act_is_from_contract act \/ act_is_from_account act.
  Proof. 
    unfold act_is_from_account, act_is_from_contract in *.
    destruct (address_is_contract (act_from act)); auto.
  Qed.

  Ltac destruct_act_from act :=
    destruct (act_from_acc_or_contract act) as [?from_contract | ?from_account]. 

  Lemma action_trace_step {from to} :
    ActionChainTrace from to ->
    from = to \/
    exists mid, inhabited (ActionChainStep from mid) /\ inhabited (ActionChainTrace mid to).
  Proof.
    intros trace. induction trace. 
    - (* clnil *)
      left; auto.
    - (* snoc *)
      destruct IHtrace as [IH | IH].
      + subst. right. exists to. split; constructor; auto. constructor.
      + destruct IH as (mid' & [step] & [trace']).
        right. exists mid'. split; constructor; auto. eapply snoc; eauto.
  Qed.

  Lemma action_trace_trans {from mid to} :
    ActionChainTrace from mid ->
    ActionChainTrace mid to ->
    inhabited (ActionChainTrace from to).
  Proof. constructor. now eapply ChainedList.clist_app. Qed.

  Lemma reachable_in_action_trace_refl {st} :
    reachable st ->
    reachable_in_action_trace st st. 
  Proof.
    unfold reachable_in_action_trace. split; auto. repeat constructor.
  Qed.

  Lemma reachable_in_action_trace_trans {from st st'} :
    reachable_in_action_trace from st ->
    ActionChainTrace st st' ->
    reachable_in_action_trace from st'.
  Proof.
    unfold reachable_in_action_trace.
    intros (? & [?]) ?. split; auto.
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  Lemma reachable_in_action_trace_step {from st st'} :
    reachable_in_action_trace from st ->
    ActionChainStep st st' ->
    reachable_in_action_trace from st'.
  Proof.
    unfold reachable_in_action_trace.
    intros (? & [trace]) step. split; auto.
    constructor.
    exact (snoc trace step).
  Qed.

  Lemma contract_addr_format_in_action_trace {from to} (addr : Address) (wc : WeakContract) :
    reachable_in_action_trace from to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros (reach & [trace]) contract_at_addr.
    remember from; induction trace; subst; cbn in *.
    { eapply contract_addr_format; eauto. }
    specialize_hypotheses.
      destruct_action_chain_step; destruct_action_eval;
        try now rewrite_environment_equiv; auto.
    rewrite_environment_equiv. cbn in *.
    destruct_address_eq; subst; cbn in *; auto.
  Qed.

Section BuildUtilsPart.

  (* This axiom states that for any reachable state and any contract it is
      decidable whether or not there is an address where the contract can be deployed to.
    This is not provable in general with the assumption ChainBase makes about
      addresses and the function address_is_contract. However, this should be
      provable in any sensible instance of ChainBase *)
  Axiom deployable_address_decidable : forall from bstate wc setup act_limit act_origin act_from amount,
    reachable_in_action_trace from bstate ->
    decidable (exists addr state, address_is_contract addr = true
              /\ env_contracts bstate addr = None
              /\ wc_init wc
                    (transfer_balance act_from addr amount bstate)
                    (build_ctx act_limit act_origin act_from addr amount amount)
                    setup = Ok state).

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
  Open Scope Z_scope.

  Local Lemma action_evaluation_decidable_in_action_trace : forall from bstate act,
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

  (* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
    from `mid` to `to`. This captures that there is a valid execution ending up in `to`
    and going through the state `mid` at some point *)
  Local Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

  (* A state is always reachable through itself *)
  Local Lemma reachable_through_refl : forall bstate,
    reachable bstate -> reachable_through bstate bstate.
  Proof.
    intros bstate reach.
    split; auto.
    do 2 constructor.
  Qed.

  (* Transitivity property of reachable_through and ChainStep *)
  Local Lemma reachable_through_trans' : forall from mid to,
    reachable_through from mid -> ChainStep mid to -> reachable_through from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  (* Transitivity property of reachable_through *)
  Local Lemma reachable_through_trans : forall from mid to,
    reachable_through from mid -> reachable_through mid to -> reachable_through from to.
  Proof.
    intros * [[trace_from] [trace_mid]] [_ [trace_to]].
    do 2 constructor.
    assumption.
    now eapply ChainedList.clist_app.
  Qed.

  (* Reachable_through can also be constructed from ChainStep instead of a
    ChainTrace since a ChainTrace can be constructed from a ChainStep *)
  Local Lemma reachable_through_step : forall from to,
    reachable from -> ChainStep from to -> reachable_through from to.
  Proof.
    intros * reach_from step.
    apply reachable_through_refl in reach_from.
    now eapply reachable_through_trans'.
  Qed.

  (* Any ChainState that is reachable through another ChainState is reachable *)
  Local Lemma reachable_through_reachable : forall from to,
    reachable_through from to -> reachable to.
  Proof.
    intros * [[trace_from] [trace_to]].
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  (* If a state is reachable then the finalized_height cannot be larger than the chain_height *)
  Local Lemma finalized_heigh_chain_height bstate :
    reachable bstate ->
    (finalized_height bstate < S (chain_height bstate))%nat.
  Proof.
    intros [trace].
    remember empty_state.
    induction trace as [ | Heq from to trace IH step ]; subst.
    - auto.
    - destruct_chain_step; try rewrite_environment_equiv; auto.
      + now inversion valid_header.
      + (* action *)
        assert (A: forall st, ActionChainTrace from st -> (finalized_height st < S (chain_height st))%nat).
        {
          intros * trace'. remember from; induction trace'; subst; auto.
          destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv; auto.
        }
        auto.
  Qed.

  (* Lemma showing that there exists a future ChainState with an added block *)
  Local Lemma add_block : forall bstate reward creator acts slot_incr,
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
  Local Lemma forward_time_exact : forall bstate reward creator slot,
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
  Local Lemma forward_time : forall bstate reward creator slot,
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

End BuildUtilsPart.

  
  Lemma action_finish_or_fail : forall (n : nat) (from st : ChainState) (acts1 acts2 : list Action),
    reachable_in_action_trace from st ->
    Forall (fun act => act_limit act = n) acts1 ->
    st.(chain_state_queue) = acts1 ++ acts2 ->
    (exists st', 
      st'.(chain_state_queue) = acts2 /\ inhabited (ActionChainTrace st st')) \/
    (exists st' act acts1',
      st'.(chain_state_queue) = act :: acts1' ++ acts2 /\ inhabited (ActionChainTrace st st') /\
      (forall bstate new_acts, ActionEvaluation st' act bstate new_acts -> False)).
  Proof.
    intro n. induction n as [|n' IHn'].
    {
      (* 0 *)
      intros * reach limits queue.
      destruct acts1 as [|act1 acts1'].
      {
        cbn. left. exists st. split; auto. repeat constructor. 
      }
      right. 
      exists st, act1, acts1'. split; auto. split.
      { repeat constructor. }
      apply Forall_cons_iff in limits as (limit & limits). intros * eval.
      destruct_action_eval; subst; cbn in *; lia.
    }
    intros from st acts1. generalize dependent st. generalize dependent from.
    induction acts1 as [|act1 acts1'].
    {
      cbn. left. exists st. split; auto. repeat constructor. 
    }
    intros * reach limits queue.
    destruct act1 as [limit origin from_addr body].
    apply Forall_cons_iff in limits as (Hlimit & limits).
    cbn in *. subst limit.
    edestruct (action_evaluation_decidable_in_action_trace from st {| act_limit := S n'; act_origin := origin; act_from := from_addr; act_body := body |}) as [(env' & new_acts & [eval]) | noeval] ; auto.
    - (* eval *)
      pose (build_chain_state env' (new_acts ++ acts1' ++ acts2)) as st'.
      assert (inhabited (ActionChainStep st st')) as [step].
      { constructor; eapply action_step_action; eauto. }
      assert (reach' : reachable_in_action_trace from st').
      {
        unfold reachable_in_action_trace. destruct reach. split; auto.
        destruct H0.
        constructor; eapply snoc; eauto.
      }
      destruct_action_eval; subst; cbn in *.
      + (* transfer *)
        specialize (IHacts1' from st' acts2 ltac:(auto) ltac:(auto) ltac:(auto)) 
          as [(finish_state & queue'' & [action_trace']) 
             | (invalid_state & act & acts' & queue_invalid & [action_trace] & no_eval)]; auto.
        * (* finish *)
          left.
          exists finish_state. split; auto. eapply action_trace_step_trace; eauto.
        * (* no finish *)
            specialize (action_trace_step_trace step action_trace) as [?]. 
            right. exists invalid_state, act, acts'. split; auto.
      + (* deploy *)
        specialize (IHacts1' from st' acts2 ltac:(auto) ltac:(auto) ltac:(auto)) 
          as [(finish_state & queue'' & [action_trace']) 
             | (invalid_state & act & acts' & queue_invalid & [action_trace] & no_eval)]; auto.
        * (* finish *)
          left.
          exists finish_state. split; auto. eapply action_trace_step_trace; eauto.
        * (* no finish *)
            specialize (action_trace_step_trace step action_trace) as [?]. 
            right. exists invalid_state, act, acts'. split; auto.
      + (* call *)
        inversion act_eq. subst. clear act_eq; cbn in *. 
        specialize (IHn' from st' (map (build_act (n' - 0) origin0 to_addr) resp_acts) (acts1' ++ acts2) ltac:(auto))
          as [(st'' & queue'' & [action_trace']) 
             | (invalid_state & act & acts' & queue_invalid & [action_trace] & no_eval)]; auto.
        {
          apply All_Forall.Forall_map; cbn in *. 
          assert (forall (f : ActionBody -> Prop) l, (forall act, f act) -> Forall f l).
          { induction l; auto. }
          eapply H. lia.
        }
        * (* finish new_acts *)
          specialize (IHacts1' from st'' acts2)as 
            [(finish_state & queue_finish & [action_trace''])
              | (invalid_state & act & acts' & queue_invalid & [action_trace''] & no_eval)]; auto.
          1: eapply reachable_in_action_trace_trans; eauto.
          -- (* finish *)
            left. exists finish_state. split; auto.
            assert (inhabited (ActionChainTrace st st')) as [?].
            { constructor. eapply snoc; eauto. constructor. }
            specialize (action_trace_trans X action_trace') as [?]. 
            specialize (action_trace_trans X0 action_trace'') as [?].
            constructor; auto. 
          -- (* no finish *)
            specialize (action_trace_trans action_trace' action_trace'') as [?]. 
            specialize (action_trace_step_trace step X) as [?]. 
            right. exists invalid_state, act, acts'. split; auto.
        * (* new_acts no finish *) 
            specialize (action_trace_step_trace step action_trace) as [?]. 
            right. exists invalid_state, act, (acts' ++ acts1'). split; auto.
            rewrite queue_invalid. rewrite app_assoc; auto.          
    - (* no eval *)
      right. unfold not in *. 
      exists st, {| act_limit := S n'; act_origin := origin; act_from := from_addr; act_body := body |}, acts1'. 
      split; auto. split.
      { repeat constructor. }
      intros * eval. apply noeval. exists bstate, new_acts. constructor; auto.
  Qed.

  Lemma one_action_finish_or_fail : forall (from st : ChainState) (act : Action) (acts : list Action),
    reachable_in_action_trace from st -> 
    st.(chain_state_queue) = act :: acts ->
    (exists st', 
      st'.(chain_state_queue) = acts /\ inhabited (ActionChainTrace st st')) \/
    (exists st' act' acts',
      st'.(chain_state_queue) = act' :: acts' ++ acts /\ inhabited (ActionChainTrace st st') /\
      (forall bstate new_acts, ActionEvaluation st' act' bstate new_acts -> False)).
  Proof.
    intros * reach queue.
    replace (act :: acts) with ([act] ++ acts) in queue by auto.
    apply (action_finish_or_fail act.(act_limit) from st [act] acts); auto.
  Qed.

  Ltac inversion_subst H := inversion H; subst; clear H.

Section ListDrop.
  Fixpoint list_drop {T : Type} (f : T -> bool) (l : list T) : list T :=
    match l with
    | [] => []
    | h :: t =>
      if f h then list_drop f t else l
    end.
 
  Lemma list_drop_le {T : Type} f (l : list T) :
    (length (list_drop f l) <= length l)%nat.
  Proof.
    induction l as [|h l' IH]; simpl; [lia|].
    destruct (f h) eqn:B; cbn in *; auto.
  Qed.

  Lemma list_drop_Forall {T : Type} f (l1 l2 : list T) :
    Forall (fun x => f x = true) l1 ->
    list_drop f (l1 ++ l2) = list_drop f l2.
  Proof.
    intros * H. induction l1; cbn in *; auto.
    apply Forall_cons_iff in H as (? & ?).
    rewrite H. auto.
  Qed.

  Lemma list_drop_contradiction {T : Type} f x (l : list T) :
    ~ x :: l = list_drop f l.
  Proof.
    intros Heq.
    pose proof (list_drop_le f l) as Hlen.
    rewrite <- Heq in Hlen. simpl in Hlen. lia.
  Qed. 

  Lemma list_drop_app_le {T : Type} f (l1 l2 : list T) :
    length (list_drop f l2) <= length (list_drop f (l1 ++ l2)).
  Proof.
    induction l1; cbn; try lia.
    destruct (f a); cbn; try lia.
    rewrite app_length.
    assert (length (list_drop f l2) <= length l2) by apply list_drop_le.
    lia.
  Qed.

End ListDrop.

Section ListDropFromContract.

  Definition list_drop_contract_action := list_drop (fun act => address_is_contract act.(act_from)).

  Lemma no_drop_from_account : forall acts,
    Forall act_is_from_account acts ->
    list_drop_contract_action (acts) = acts.
  Proof.
    destruct acts; cbn; auto.
    intro. apply Forall_cons_iff in H as [H1 H2]. unfold act_is_from_account in *. rewrite H1. auto.
  Qed.

  Lemma drop_from_contract : forall new_acts acts,
    Forall act_is_from_contract new_acts ->
    list_drop_contract_action (new_acts ++ acts) = list_drop_contract_action acts.
  Proof.
    intro new_acts. induction new_acts as [|a new_acts' IH]; cbn; auto.
    intros * from_contracts. apply Forall_cons_iff in from_contracts as (? & ?).
    unfold act_is_from_contract in *. rewrite H. apply IH; auto.
  Qed.

  Lemma drop_until_from_account : forall new_acts acts,
    Forall act_is_from_contract new_acts ->
    Forall act_is_from_account acts ->
    list_drop_contract_action (new_acts ++ acts) = acts.
  Proof.
    intro new_acts. induction new_acts as [|a new_acts' IH]; cbn; auto.
    - intros. apply no_drop_from_account; auto.
    - intros. apply Forall_cons_iff in H as [H1 H2]. unfold act_is_from_contract in *.
      rewrite H1. apply IH; auto.
  Qed.

  Lemma forall_list_drop (acts : list Action) :
    Forall act_is_from_account acts ->
    Forall act_is_from_account (list_drop_contract_action acts).
  Proof.
    intros. destruct acts; cbn; auto. apply Forall_cons_iff in H as (? & ?).
    unfold act_is_from_account in *. rewrite H. constructor; auto.
  Qed.
 
  Lemma list_drop_contract_action_len acts :
    (length (list_drop_contract_action acts) <= length acts)%nat.
  Proof.
    induction acts as [|a acts' IH]; simpl; [lia|].
    destruct (address_is_contract (act_from a)) eqn:B; cbn in *.
    - rewrite B. lia. (* eapply le_trans; [apply IH|]. eapply le_S, le_n. *)
    - rewrite B. cbn. lia.
  Qed.

  Lemma list_drop_contract_contradiction act acts :
    ~ act :: acts = list_drop_contract_action acts.
  Proof.
    intros Heq.
    pose proof (list_drop_contract_action_len acts) as Hlen.
    rewrite <- Heq in Hlen. simpl in Hlen. lia.
  Qed. 

  Lemma list_drop_contract_app_le acts1 acts2 :
    length (list_drop_contract_action acts2) <= 
      length (list_drop_contract_action (acts1 ++ acts2)).
  Proof.
    unfold list_drop_contract_action.
    apply list_drop_app_le.
  Qed.

End ListDropFromContract.

  Lemma emited_acts_from_is_always_contract :
    forall {from bstate : ChainState}
           {act : Action}
           {acts : list Action}
           {next_env : Environment}
           {new_acts : list Action},
      reachable_in_action_trace from bstate ->
      bstate.(chain_state_queue) = act :: acts ->
      ActionEvaluation bstate act next_env new_acts ->
      Forall act_is_from_contract new_acts.
  Proof.
    intros * reach queue eval.
    destruct_action_eval; subst; auto.
    apply All_Forall.Forall_map. unfold act_is_from_contract. cbn.
    apply Forall_forall.
    apply (contract_addr_format_in_action_trace to_addr wc reach) in deployed.
    auto.
  Qed.

  (* general *)
  Local Lemma list_app_eq_tl : forall (T : Type) (l l1 l2: list T), 
    l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    assert (rev_injective : forall (T: Type) (l1 l2: list T), rev l1 = rev l2 -> l1 = l2).
    {
      intros T l1 l2. intro H.
      rewrite <- rev_involutive.
      rewrite <- H.
      rewrite -> rev_involutive.
      reflexivity.
    }
    assert (list_app_eq1 : forall (T: Type) (l l1 l2: list T), l ++ l1 = l ++ l2 -> l1 = l2).
    {
      intros T l. induction l as [|h l' IHl'].
      - simpl. intros. apply H.
      - simpl. intros. apply IHl'. injection H. intro goal. apply goal.
    }
    intros T l.  
    destruct l as [|h l'].
    - intros l1 l2. 
      rewrite app_nil_r. rewrite app_nil_r. intro H. apply H.
    - intros l1 l2 H.
      rewrite <- rev_involutive with T (l1 ++ h :: l') in H.
      rewrite <- rev_involutive with T (l2 ++ h :: l') in H.
      apply rev_injective in H.
      rewrite rev_app_distr in H. rewrite rev_app_distr in H.
      apply list_app_eq1 in H. apply rev_injective in H. apply H.
  Qed.

  Lemma action_step_external_equiv :
    forall {origin prev1 prev2 next1 : ChainState},
      reachable_in_action_trace origin prev1 ->
      reachable_in_action_trace origin prev2 ->
      ActionChainStep prev1 next1 ->
      EnvironmentEquiv prev1 prev2 ->
      prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
      (exists (next2 : ChainState),
        EnvironmentEquiv next1 next2 /\
        next1.(chain_state_queue) = next2.(chain_state_queue) /\
        inhabited (ActionChainStep prev2 next2)).
  Proof.
    intros * reach_th1 reach_th2 step env_eq queue_eq.
    destruct_action_chain_step; destruct_action_eval.
    - (* transfer *)
      rewrite_environment_equiv;
      rewrite_queue; subst; cbn in *.
      pose (build_chain_state (transfer_balance from_addr to_addr amount prev2) acts) as next2.
      exists next2.
      split; auto. split; auto.
      assert (inhabited (ActionEvaluation prev2
        {|  act_limit := limit;
            act_origin := origin0;
            act_from := from_addr;
            act_body := act_transfer to_addr amount |}
        (transfer_balance from_addr to_addr amount prev2) [])) as [eval].
      { constructor. eapply eval_transfer; eauto. reflexivity. }
      constructor. eapply action_step_action; eauto.
    - (* deploy *)
      rewrite_environment_equiv;
      rewrite_queue; subst; cbn in *.
      pose (build_chain_state (set_contract_state to_addr state
               (add_contract to_addr wc
                  (transfer_balance from_addr to_addr amount prev2))) acts) as next2.
      exists next2.
      split; auto. split; auto.
      assert (inhabited (ActionEvaluation prev2
        {| act_limit := limit;
           act_origin := origin0;
           act_from := from_addr;
           act_body := act_deploy amount wc setup |}
        (set_contract_state to_addr state
               (add_contract to_addr wc
                  (transfer_balance from_addr to_addr amount prev2))) [])) as [eval].
      { constructor. eapply eval_deploy; eauto. reflexivity. }
      constructor. eapply action_step_action; eauto.      
    - (* call *)
      rewrite_environment_equiv.
      pose (build_chain_state 
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev2)) 
        ( map (build_act (limit - 1) origin0 to_addr) resp_acts ++ acts)) as next2.
      exists next2.
      split; auto. split. subst; rewrite_queue; auto.
      assert (inhabited (ActionEvaluation prev2
        {| act_limit := limit;
           act_origin := origin0;
           act_from := from_addr;
           act_body :=
            match msg with
            | Some msg => act_call to_addr amount msg
            | None => act_transfer to_addr amount
            end |}
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev2))
        (map (build_act (limit - 1) origin0 to_addr) resp_acts))) as [eval].
      { constructor. eapply eval_call; eauto. rewrite_environment_equiv. apply receive_some. reflexivity. }
      constructor. rewrite_queue. 
      eapply action_step_action; eauto; rewrite_queue; subst. auto.      
  Qed. 

  Fixpoint action_trace_length {from to} (action_trace : ActionChainTrace from to) : nat :=
    match action_trace with
    | clnil => 0%nat
    | snoc trace' _ => S (action_trace_length trace') 
    end.
  
  Lemma action_trace_external_equiv_strong : 
    forall 
           {origin from1 from2 to1 : ChainState}
           (trace1 : ActionChainTrace from1 to1),
      reachable_in_action_trace origin from1 ->
      reachable_in_action_trace origin from2 ->
      EnvironmentEquiv from1 from2 ->
      from1.(chain_state_queue) = from2.(chain_state_queue) ->
      (exists (to2 : ChainState) (trace2 : ActionChainTrace from2 to2),
        EnvironmentEquiv to1 to2 /\
        to1.(chain_state_queue) = to2.(chain_state_queue) /\
        action_trace_length trace1 = action_trace_length trace2 ).
  Proof.
    intros * reach_th1 reach_th2 env_eq queue_eq.
    induction (trace1) as [|from1 mid1 to1 action_trace1' IHtrace1 step1]; cbn in *; subst.
    {
      (* clnil *)
      exists from2, clnil. split; auto. 
    }
    specialize_hypotheses. 
    destruct IHtrace1 as (mid2 & action_trace2' & env_eq_mid & queue_eq_mid & Hlen).
    assert (reach_th1' : reachable_in_action_trace origin mid1).
    { eapply (reachable_in_action_trace_trans reach_th1); eauto. }
    assert (reach_th2' : reachable_in_action_trace origin mid2).
    { eapply (reachable_in_action_trace_trans reach_th2); eauto. }
    specialize (action_step_external_equiv reach_th1' reach_th2' step1 ltac:(auto) ltac:(auto))
      as (to2 & env_eq_to & queue_eq_to & [step2]).
    exists to2, (snoc action_trace2' step2). 
    split; auto. split; cbn; auto. 
  Qed.

  Local Hint Unfold reachable_in_action_trace : core.

  Axiom deploy_address_deterministic : 
    forall {prev : ChainState}
           {next1 next2 : ChainState}
           {limit : nat}
           {origin from_addr to_addr1 to_addr2 : Address}
           {amount : Amount}
           {wc : WeakContract}
           {setup : SerializedValue}
           {state1 state2 : SerializedValue},
      let act := build_act limit origin from_addr (act_deploy amount wc setup) in
      ActionEvaluation prev act next1 [] ->
      ActionEvaluation prev act next2 [] ->
      EnvironmentEquiv
        next1
        (set_contract_state
          to_addr1 state1 (add_contract
                      to_addr1 wc (transfer_balance from_addr to_addr1 amount prev))) ->
      EnvironmentEquiv
        next2
        (set_contract_state
          to_addr2 state2 (add_contract
                      to_addr2 wc (transfer_balance from_addr to_addr2 amount prev))) ->    
      to_addr1 = to_addr2.

  Lemma action_step_weak_deterministic {from prev next1 next2} : 
    reachable_in_action_trace from prev ->
    ActionChainStep prev next1 ->
    ActionChainStep prev next2 ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * (reach & [action_trace]). intros. 
    repeat destruct_action_chain_step.
    rewrite queue_prev in *. inversion queue_prev0. subst act0 acts0. clear queue_prev0.
    destruct_action_eval; destruct_action_eval; subst act; cbn in *; 
      try repeat rewrite_environment_equiv; try congruence.
    - (* transfer *)
      subst; cbn in *. split. 2: rewrite_queue; auto.
      inversion act_eq; subst.
      reflexivity. 
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion_subst act_eq.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto. 
      congruence.
    - (* deploy *)
      inversion_subst act_eq.
      pose (build_act limit origin from_addr (act_deploy amount wc setup)) as act.
      assert (ActionEvaluation prev act next1 []) as eval1.
      { eapply (eval_deploy limit origin from_addr to_addr0); eauto. }
      assert (ActionEvaluation prev act next2 []) as eval2.
      { eapply (eval_deploy limit origin from_addr to_addr); eauto. }
      specialize (deploy_address_deterministic eval1 eval2 env_eq0 env_eq) as addr_eq; subst.
      rewrite init_some in init_some0. inversion_subst init_some0. 
      split. reflexivity. rewrite_queue. auto. 
    - destruct msg; congruence.
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion H3. subst.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto.
      congruence.
    - destruct msg; congruence.
    - destruct msg0; destruct msg; try congruence.
      + 
        inversion act_eq; subst; clear act_eq ; cbn in *.
        rewrite deployed0 in *. inversion deployed; subst; clear deployed.
        rewrite deployed_state0 in *. inversion deployed_state; subst; clear deployed_state.
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
      + 
        inversion_subst act_eq; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed.
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
  Qed.  

  Lemma action_trace_no_branch : forall {from st st1 st2}
      (trace1 : ActionChainTrace st st1)
      (trace2 : ActionChainTrace st st2),
    reachable_in_action_trace from st ->
    (exists (st2' : ChainState) (trace12 : ActionChainTrace st1 st2'),
        EnvironmentEquiv st2 st2'  /\
        st2.(chain_state_queue) = st2'.(chain_state_queue)) \/ 
    (exists (st1' : ChainState) (trace21 : ActionChainTrace st2 st1'),
        EnvironmentEquiv st1 st1'  /\
        st1.(chain_state_queue) = st1'.(chain_state_queue)).        
  Proof.
    intros from st st1 st2 trace1.
    generalize dependent st2.
    remember st; induction trace1 as [|from1 mid1 to1 trace1' IHtrace1 step1]; subst.
    {
      (* clnil *)
      intros * trace2 reach. 
      left. exists st2, trace2. split; auto. reflexivity.
    }
    intros * trace2 reach.
    specialize (IHtrace1 ltac:(auto) st2 trace2 ltac:(auto)) as [IH|IH].
    {
      (* mid1 -> st2' *)
      destruct IH as (st2' & trace12 & env_eq & queue_eq).
      destruct (action_trace_step trace12) as [|(to1' & [step1'] & [trace12'])]; subst.
      {
        (* mid1 = st2' *) (* st2 -> to' *)
        assert (reach_st2 : reachable_in_action_trace from st2).
        { apply (reachable_in_action_trace_trans reach trace2). }
        assert (reach_st2' : reachable_in_action_trace from st2').
        { apply (reachable_in_action_trace_trans reach trace1'). }
        specialize (action_step_external_equiv reach_st2' reach_st2 step1 
          ltac:(rewrite_environment_equiv; reflexivity) ltac:(auto))
          as (to1' & env_eq_to & queue_eq_to & [step']).
        right.
        exists to1', (snoc clnil step').
        split; auto.  
      }
      {
        (* to1 -> st2'' *)
        assert (reach_mid1 : reachable_in_action_trace from mid1).
        { apply (reachable_in_action_trace_trans reach trace1'). }
        assert (reach_to1 : reachable_in_action_trace from to1).
        { apply (reachable_in_action_trace_step reach_mid1 step1). } 
        assert (reach_to1' : reachable_in_action_trace from to1').
        { apply (reachable_in_action_trace_step reach_mid1 step1'). } 
        specialize (action_step_weak_deterministic reach_mid1 step1 step1')
          as (env_eq_to & queue_eq_to).       
        specialize (action_trace_external_equiv_strong trace12' reach_to1' reach_to1 
          ltac:(rewrite_environment_equiv; reflexivity) ltac:(auto))
          as (st2'' & trace12'' & env_eq' & queue_eq' & _).
        left.
        exists st2'', trace12''. split.
        rewrite_environment_equiv. auto. rewrite_queue. auto.  
      }
    }
    (* mid1 -> st2' *)
    destruct IH as (mid1' & trace21 & env_eq & queue_eq).
    assert (reach_mid1 : reachable_in_action_trace from mid1).
    { apply (reachable_in_action_trace_trans reach trace1'). }
    assert (reach_mid1' : reachable_in_action_trace from mid1').
    { 
      assert (reach_st2 : reachable_in_action_trace from st2).
      { apply (reachable_in_action_trace_trans reach trace2). }
      apply (reachable_in_action_trace_trans reach_st2 trace21). }
    specialize (action_step_external_equiv reach_mid1 reach_mid1' step1
      ltac:(rewrite_environment_equiv; reflexivity) ltac:(auto))
          as (to1' & env_eq' & queue_eq' & [step]).
    right.
    exists to1', (snoc trace21 step).
    split; auto.
  Qed.

  
  Lemma action_step_drop_le {from prev next} :
    reachable_in_action_trace from prev ->
    ActionChainStep prev next ->
    length (list_drop_contract_action next.(chain_state_queue)) 
      <= length (list_drop_contract_action prev.(chain_state_queue)).
  Proof. 
    intros reach step. destruct_action_chain_step.
    specialize (emited_acts_from_is_always_contract reach queue_prev eval)
      as from_contracts.
    destruct_action_eval; subst; rewrite_queue; cbn in *; 
      try rewrite Nat.ltb_irrefl; cbn.
    - (* transfer *)
      assert (length (list_drop_contract_action acts) <= length acts). 
      apply list_drop_contract_action_len. 
      destruct (address_is_contract from_addr); cbn; lia.  
    - (* deploy *)
      assert (length (list_drop_contract_action acts) <= length acts). 
      apply list_drop_contract_action_len. 
      destruct (address_is_contract from_addr); cbn; lia.    
    - (* call *)
      assert (length (list_drop_contract_action acts) <= length acts). 
      apply list_drop_contract_action_len.
      rewrite (drop_from_contract); auto.
      destruct (address_is_contract from_addr); cbn; lia.   
  Qed.  

  Lemma action_trace_drop_le {from st st'} :
    reachable_in_action_trace from st ->
    ActionChainTrace st st' ->
    length (list_drop_contract_action st'.(chain_state_queue)) 
      <= length (list_drop_contract_action st.(chain_state_queue)).
  Proof. 
    intros reach trace. 
    remember st; induction trace; subst.
    - (* clnil *) 
      lia. 
    - (* snoc *)
      assert (reach_mid : reachable_in_action_trace from mid).
      { apply (reachable_in_action_trace_trans reach); auto. }
      assert (length
            (list_drop_contract_action
               (chain_state_queue
                  to)) <=
          length
            (list_drop_contract_action
               (chain_state_queue
                  mid))).
      apply (action_step_drop_le reach_mid l).
      specialize_hypotheses. lia.
  Qed.  

  Lemma action_finish_decidable : forall (st : ChainState) act acts,
    reachable st ->
    st.(chain_state_queue) = act :: acts ->
    (exists st', 
      st'.(chain_state_queue) = acts /\ inhabited (ActionChainTrace st st')) \/
    (forall st',
      ~ (st'.(chain_state_queue) = acts /\ inhabited (ActionChainTrace st st'))).
  Proof.
    intros * reach queue.
    assert (reach_th : reachable_in_action_trace st st).
    {
      unfold reachable_in_action_trace. split; auto.
      repeat constructor.
    }
    specialize (queue_from_account st reach) as from_accs.
    specialize (one_action_finish_or_fail st st act acts reach_th queue)
      as [(finish & queue_finish & [trace_finish])
          |(st1 & act1 & acts1 & queue1 & [trace1] & noeval)].
    - (* finish *)
      left. exists finish. split; auto.
    - (* fail *)
      right. rewrite_queue. 
      apply Forall_cons_iff in from_accs as (from_acc & from_accs).
      unfold not.
      intros finish (queue_finish & [trace_finish]).
      specialize (action_trace_no_branch trace_finish trace1 reach_th)
        as [(st1' & trace_finish_1 & env_eq' & queue')
           |(finish' & trace_1_finish & env_eq' & queue')].
      + (* finish -> 1 *)
        assert (reach_finish : reachable_in_action_trace st finish).
        { apply (reachable_in_action_trace_trans reach_th); auto. }
        destruct (action_trace_step trace_finish_1)
          as [|(next & [step_next] & [trace_next])]; subst.
        * rewrite queue' in *.  
          rewrite app_comm_cons in queue1. solve_list_contra.
        * assert (reach_next : reachable_in_action_trace st next).
          apply (reachable_in_action_trace_step reach_finish step_next).
          destruct_action_chain_step. rewrite_queue.
          specialize (action_trace_drop_le reach_next trace_next)
            as Hle.
          (* apply Forall_cons_iff in from_accs as (from_acc' & from_accs).  *)
          specialize (emited_acts_from_is_always_contract reach_finish queue_prev eval) as from_contracts.
          rewrite_queue.
          rewrite drop_from_contract in Hle; auto. rewrite app_comm_cons in Hle.
          assert (Hle' : length (list_drop_contract_action (act0 :: acts)) <= length
        (list_drop_contract_action
           ((act1 :: acts1) ++ act0 :: acts))).
          { unfold list_drop_contract_action. apply list_drop_app_le. }    
          assert (Hle'' : length (list_drop_contract_action (act0 :: acts)) <= length (list_drop_contract_action acts)) by lia.
          rewrite no_drop_from_account in Hle''; auto.
          apply Forall_cons_iff in from_accs as (_ & from_accs).
          rewrite no_drop_from_account in Hle''; auto. cbn in *. lia. 
      + (* 1 -> finish *) 
        destruct (action_trace_step trace_1_finish)
          as [|(next & [step_next] & [trace_next])]; subst.
        * rewrite app_comm_cons in queue1. rewrite queue' in *. solve_list_contra.
        * destruct_action_chain_step.
          rewrite_queue. inversion_subst queue1.
          apply (noeval next new_acts); auto.
  Qed.


  Axiom user_address_exists : forall (bstate : ChainState), 
    reachable bstate ->
    exists (user : Address), 
      address_is_contract user = false.

  (* serialization [totality] of (modified) ChainStep *)
  Lemma chain_step_serial : forall st : ChainState,
    reachable st ->
    exists st', inhabited (ChainStep st st').
  Proof.  
    intros * reach.
    destruct (chain_state_queue st) as [| act acts] eqn:queue.
    - (* queue = [] *) (* step_block *)
      destruct (user_address_exists st) as (creater & ?); auto. 
      destruct (forward_time st 0 creater (S st.(current_slot))) 
        as (st' & header & H1 & H2 & H3 & H4 & H5); auto; try lia.
      exists st'. constructor. 
      apply (step_block st st' header); eauto; try (rewrite H4; auto).
    - (* queue = act :: act' *)
      specialize (action_finish_decidable st act acts) 
        as [(finish & queue' & [trace])| no_finish]; auto.
      * (* step_action *)
        exists finish. constructor.
        eapply step_action; eauto.
      * (* step_action_invalid *)
        pose (build_chain_state st.(chain_state_env) acts) as st'.
        exists st'.
        constructor. eapply step_action_invalid; eauto.
        1: subst; cbn; reflexivity.
        intros.
        apply (no_finish bstate). split; auto.
  Qed.

  Inductive ActionChainTraceEquiv
    : (forall {from1 from2 to1 to2}, 
        ActionChainTrace from1 to1 -> ActionChainTrace from2 to2 -> Prop) :=
  | at_equiv_clnil {p1 p2 : ChainState} : 
      ActionChainTraceEquiv (@clnil ChainState ActionChainStep p1) 
                            (@clnil ChainState ActionChainStep p2)
  | at_equiv_snoc {from1 from2 mid1 mid2 to1 to2 : ChainState} 
                  {trace1 : ActionChainTrace from1 mid1} 
                  {trace2 : ActionChainTrace from2 mid2} 
                  {step1 : ActionChainStep mid1 to1} 
                  {step2 : ActionChainStep mid2 to2} :
      EnvironmentEquiv to1 to2 ->
      to1.(chain_state_queue) = to2.(chain_state_queue) ->
      ActionChainTraceEquiv trace1 trace2 ->
      ActionChainTraceEquiv (snoc trace1 step1) (snoc trace2 step2).

  Lemma action_chain_step_no_refl_strong {st st': ChainState} :  
    ActionChainStep st st' ->  
    st.(chain_state_queue) = st'.(chain_state_queue) ->
    False.
  Proof.
    intros step queue_eq.
    destruct_action_chain_step. destruct_action_eval; subst.
    - rewrite_queue. cbn in *. solve_list_contra. 
    - rewrite_queue. cbn in *; solve_list_contra.
    - rewrite_queue. 
      replace ({|
                act_limit := limit;
                act_origin := origin;
                act_from := from_addr;
                act_body :=
                  match msg with
                  | Some msg => act_call to_addr amount msg
                  | None => act_transfer to_addr amount
                  end
                |} :: acts) 
        with ([{|
               act_limit := limit;
               act_origin := origin;
               act_from := from_addr;
               act_body :=
                 match msg with
                 | Some msg => act_call to_addr amount msg
                 | None => act_transfer to_addr amount
                 end
             |}] ++ acts) in queue_prev by auto.
    apply list_app_eq_tl in queue_prev.
    destruct resp_acts; cbn in *; try congruence.
    inversion queue_prev. lia. 
  Qed.

  
  Lemma action_trace_weak_determin_nth : 
    forall (from st1 st2 : ChainState) 
           (trace1 : ActionChainTrace from st1)
           (trace2 : ActionChainTrace from st2),
    reachable from ->
    action_trace_length trace1 = action_trace_length trace2 ->
    EnvironmentEquiv st1 st2 /\
    st1.(chain_state_queue) = st2.(chain_state_queue).
  Proof.
    intros * reach.    
    intros Hlen. remember (action_trace_length trace1) as n.
    generalize dependent Hlen.
    generalize dependent Heqn.
    generalize dependent trace2.
    generalize dependent trace1.
    generalize dependent st2.
    generalize dependent st1.
    induction n. 
    {
      (* 0 *)
      intros.
      destruct trace1; cbn in *; try congruence.
      destruct trace2; cbn in *; try congruence. split. reflexivity. auto.
    }
    intros.
    destruct trace1; cbn in *; try congruence.
    destruct trace2; cbn in *; try congruence.
    destruct (IHn mid mid0 trace1 trace2) as (env_eq & queue_eq); auto.
    clear IHn.
    destruct_action_chain_step; destruct_action_chain_step.
    destruct_action_eval; destruct_action_eval; subst; rewrite_queue; cbn in *; 
      try repeat rewrite_environment_equiv; try congruence.  
    - (* transfer *)
      subst; cbn in *. inversion_subst queue_prev0. split. reflexivity. auto.
    - (* contra *)
      inversion_subst queue_prev0.
      destruct msg; try congruence. inversion_subst H3. 
      assert (address_is_contract to_addr0 = true). 
      eapply contract_addr_format_in_action_trace; eauto. 
      congruence.
    - (* deploy *)
      apply eq_sym in queue_prev0. inversion_subst queue_prev0; cbn in *. 
      pose (build_act limit origin from_addr (act_deploy amount wc setup)) as act.
      assert (ActionEvaluation mid0 act to []) as eval1.
      { eapply (eval_deploy limit origin from_addr to_addr0); eauto. }
      assert (ActionEvaluation mid0 act to0 []) as eval2.
      { eapply (eval_deploy limit origin from_addr to_addr); eauto. }
      specialize (deploy_address_deterministic eval1 eval2 env_eq1 env_eq0) as addr_eq; subst.
      subst.
      rewrite init_some in *. inversion_subst init_some0. 
      split. reflexivity. auto.
    - (* contra *)
      destruct msg; congruence.
    - (* contra *)
      inversion_subst queue_prev0.
      destruct msg; try congruence. inversion_subst H3. 
      assert (address_is_contract to_addr0 = true). 
      eapply contract_addr_format_in_action_trace; eauto. congruence. 
    - (* contra *)
      destruct msg; congruence.
    - (* call *)
      destruct msg0; destruct msg; try congruence.
      + 
        inversion_subst queue_prev0 ; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed. 
        rewrite deployed_state0 in *. inversion_subst deployed_state.
        rewrite (address_eq_refl to_addr0) in *.
        destruct (address_eqb to_addr0 from_addr0); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
      + 
        inversion_subst queue_prev0; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed.
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite (address_eq_refl to_addr0) in *.
        destruct (address_eqb to_addr0 from_addr0); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto. 
  Qed.

  Lemma action_trace_equiv_length_iff : 
    forall (from st1 st2 : ChainState) 
           (trace1 : ActionChainTrace from st1)
           (trace2 : ActionChainTrace from st2),
      reachable from ->
      ActionChainTraceEquiv trace1 trace2 <-> 
        action_trace_length trace1 = action_trace_length trace2.
  Proof.
    intros * reach. split.
    { intros trace_equiv. induction trace_equiv; cbn; auto. }
    intros Hlen. remember (action_trace_length trace1) as n.
    generalize dependent Hlen.
    generalize dependent Heqn.
    generalize dependent trace2.
    generalize dependent trace1.
    generalize dependent st2.
    generalize dependent st1.
    induction n. 
    {
      (* clnil *)
      intros.
      destruct trace1; cbn in *; try congruence.
      destruct trace2; cbn in *; try congruence. 
      constructor.
    }
    intros.
    destruct trace1 as [| ? ? ? ?]; subst; cbn in *; try congruence.
    destruct trace2 as [| ? ? ? ?]; subst; cbn in *; try congruence.
    specialize (IHn mid mid0 trace1 trace2 ltac:(auto) ltac:(auto)).
    specialize (action_trace_weak_determin_nth from to to0 (snoc trace1 a) (snoc trace2 a0) ltac:(auto))
      as (? & ?); cbn; try lia.
    apply at_equiv_snoc; auto.
  Qed. 

  Fixpoint clist_length {Point} {Link} {from to} 
      (cl : ChainedList Point Link from to) : nat :=
    match cl with
    | clnil => 0%nat
    | snoc cl' _ => S (clist_length cl') 
    end.

  Lemma clist_length_app {Point} {Link}
      {c1 c2 c3}
      (xs : ChainedList Point Link c1 c2)
      (ys : ChainedList Point Link c2 c3) :
    clist_length (clist_app xs ys) =  clist_length xs + clist_length ys.
  Proof.
    induction ys; cbn.
    - lia. 
    - replace (clist_length xs + S (clist_length ys)) with 
        (S (clist_length xs + clist_length ys)) by lia.
      auto.
  Qed. 

  Definition action_trace_length' {from to} : ActionChainTrace from to -> nat := clist_length.

  
  Lemma action_trace_weak_determin_nth' : 
    forall (from st1 st2 : ChainState) 
           (trace1 : ActionChainTrace from st1)
           (trace2 : ActionChainTrace from st2),
    reachable from ->
    action_trace_length' trace1 = action_trace_length' trace2 ->
    EnvironmentEquiv st1 st2 /\
    st1.(chain_state_queue) = st2.(chain_state_queue).
  Proof.
    intros * reach.    
    intros Hlen. remember (action_trace_length' trace1) as n.
    generalize dependent Hlen.
    generalize dependent Heqn.
    generalize dependent trace2.
    generalize dependent trace1.
    generalize dependent st2.
    generalize dependent st1.
    induction n. 
    {
      (* 0 *)
      intros.
      destruct trace1; cbn in *; try congruence.
      destruct trace2; cbn in *; try congruence. split. reflexivity. auto.
    }
    intros.
    destruct trace1; cbn in *; try congruence.
    destruct trace2; cbn in *; try congruence.
    destruct (IHn mid mid0 trace1 trace2) as (env_eq & queue_eq); auto.
    clear IHn.
    destruct_action_chain_step; destruct_action_chain_step.
    destruct_action_eval; destruct_action_eval; subst; rewrite_queue; cbn in *; 
      try repeat rewrite_environment_equiv; try congruence.  
    - (* transfer *)
      subst; cbn in *. inversion_subst queue_prev0. split. reflexivity. auto.
    - (* contra *)
      inversion_subst queue_prev0.
      destruct msg; try congruence. inversion_subst H3. 
      assert (address_is_contract to_addr0 = true). 
      eapply contract_addr_format_in_action_trace; eauto. 
      congruence.
    - (* deploy *)
      apply eq_sym in queue_prev0. inversion_subst queue_prev0; cbn in *. 
      pose (build_act limit origin from_addr (act_deploy amount wc setup)) as act.
      assert (ActionEvaluation mid0 act to []) as eval1.
      { eapply (eval_deploy limit origin from_addr to_addr0); eauto. }
      assert (ActionEvaluation mid0 act to0 []) as eval2.
      { eapply (eval_deploy limit origin from_addr to_addr); eauto. }
      specialize (deploy_address_deterministic eval1 eval2 env_eq1 env_eq0) as addr_eq; subst.
      subst.
      rewrite init_some in *. inversion_subst init_some0. 
      split. reflexivity. auto.
    - (* contra *)
      destruct msg; congruence.
    - (* contra *)
      inversion_subst queue_prev0.
      destruct msg; try congruence. inversion_subst H3. 
      assert (address_is_contract to_addr0 = true). 
      eapply contract_addr_format_in_action_trace; eauto. congruence. 
    - (* contra *)
      destruct msg; congruence.
    - (* call *)
      destruct msg0; destruct msg; try congruence.
      + 
        inversion_subst queue_prev0 ; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed. 
        rewrite deployed_state0 in *. inversion_subst deployed_state.
        rewrite (address_eq_refl to_addr0) in *.
        destruct (address_eqb to_addr0 from_addr0); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
      +  
        inversion_subst queue_prev0; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed.
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite (address_eq_refl to_addr0) in *.
        destruct (address_eqb to_addr0 from_addr0); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split. reflexivity. auto. 
  Qed.

  Lemma action_trace_equiv_length_iff' : 
    forall (from st1 st2 : ChainState) 
           (trace1 : ActionChainTrace from st1)
           (trace2 : ActionChainTrace from st2),
      reachable from ->
      ActionChainTraceEquiv trace1 trace2 <-> 
        action_trace_length' trace1 = action_trace_length' trace2.
  Proof.
    intros * reach. split.
    { intros trace_equiv. induction trace_equiv; cbn; auto. }
    intros Hlen. remember (action_trace_length trace1) as n.
    generalize dependent Hlen.
    generalize dependent Heqn.
    generalize dependent trace2.
    generalize dependent trace1.
    generalize dependent st2.
    generalize dependent st1.
    induction n. 
    {
      (* clnil *)
      intros.
      destruct trace1; cbn in *; try congruence.
      destruct trace2; cbn in *; try congruence. 
      constructor.
    }
    intros.
    destruct trace1 as [| ? ? ? ?]; subst; cbn in *; try congruence.
    destruct trace2 as [| ? ? ? ?]; subst; cbn in *; try congruence.
    specialize (IHn mid mid0 trace1 trace2 ltac:(auto) ltac:(auto)).
    specialize (action_trace_weak_determin_nth' from to to0 (snoc trace1 a) (snoc trace2 a0) ltac:(auto))
      as (? & ?); cbn; try lia.
    apply at_equiv_snoc; auto.
  Qed. 

  Lemma action_trace_step' {from to}
    (trace : ActionChainTrace from to) :
    action_trace_length' trace = 0 \/
    (* trace = clnil \/ *)
    exists mid (step : ActionChainStep from mid) (trace' : ActionChainTrace mid to),
      clist_app (snoc clnil step) trace' = trace.
  Proof.
    induction trace. 
    - (* clnil *)
      left; auto.
    - (* snoc *)
      destruct IHtrace as [IH | IH].
      + remember from; destruct trace; cbn in *; try lia. 
        right. exists to, l, clnil. cbn. auto.  
      + destruct IH as (from' & step & trace' & Htrace).
        right.
        exists from', step, (snoc trace' l).
        cbn in *.
        rewrite Htrace.
        auto.
  Qed.

  Lemma action_step_determin {origin_bstate prev1 prev2 next1 next2} : 
    ActionChainStep prev1 next1 ->
    ActionChainStep prev2 next2 ->
    reachable_in_action_trace origin_bstate prev1 ->
    reachable_in_action_trace origin_bstate prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * step1 step2 (reach & [action_trace1]) (_ & [action_trace2])
      env_eq queue_eq.  
    repeat destruct_action_chain_step. 
    rewrite_queue. inversion_subst queue_prev0.
    destruct_action_eval; destruct_action_eval; subst act0; cbn in *; 
      try repeat rewrite_environment_equiv; try congruence.
    - (* transfer *)
      subst; cbn in *. split. 2: rewrite_queue; auto.
      inversion act_eq; subst.
      reflexivity. 
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion_subst act_eq.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto. 
      congruence.
    - (* deploy *)
      inversion_subst act_eq. cbn in *. split; auto.
      pose (build_act limit origin from_addr (act_deploy amount wc setup)) as act.
      assert (ActionEvaluation prev2 act next1 []) as eval1.
      { eapply (eval_deploy limit origin from_addr to_addr0);
         eauto. }
      assert (ActionEvaluation prev2 act next2 []) as eval2.
      { eapply (eval_deploy limit origin from_addr to_addr); 
         eauto. }
      specialize (deploy_address_deterministic eval1 eval2 env_eq1 env_eq0) as addr_eq; subst.
      rewrite init_some in init_some0. inversion_subst init_some0. 
      reflexivity.
    - destruct msg; congruence.
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion H3. subst.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto.
      congruence.
    - destruct msg; congruence.
    - destruct msg0; destruct msg; try congruence.
      + 
        inversion act_eq; subst; clear act_eq ; cbn in *.
        rewrite deployed0 in *. inversion deployed; subst; clear deployed.
        rewrite deployed_state0 in *. inversion deployed_state; subst; clear deployed_state.
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
      + 
        inversion_subst act_eq; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed.
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
  Qed.  

  Lemma no_cyclic_action_trace_strong {from mid to} :
    reachable from ->
    ActionChainTrace from mid ->
    ActionChainStep mid to ->
    from.(chain_state_queue) = to.(chain_state_queue) -> 
    False.
  Proof.
    intros reach trace step queue_eq.
    assert (reach_at : reachable_in_action_trace from from) by (apply reachable_in_action_trace_refl; auto). 
    destruct (action_trace_step' trace) as [|(st1 & step1 & trace1 & trace_eq1)].
    {
      destruct trace; cbn in *; try lia. 
      eapply (action_chain_step_no_refl_strong step); eauto.
    }
    specialize (queue_from_account from reach) as from_accs.
    
    assert (reach1 : reachable_in_action_trace from st1). eapply reachable_in_action_trace_step; eauto.
    destruct_action_chain_step. rewrite_queue.
    pose (snoc trace1 step) as trace_st1_from.
    specialize (action_trace_drop_le reach1 trace_st1_from) as Hle.
    rewrite_queue.
    specialize (emited_acts_from_is_always_contract reach_at queue_prev eval) as from_contracts.
    rewrite drop_from_contract in Hle; auto.
    rewrite <- queue_eq in *.
    rewrite no_drop_from_account in Hle; auto.
    rewrite no_drop_from_account in Hle. 2: eapply Forall_cons_iff; eauto.
    cbn in *. lia.
  Qed. 

  Lemma action_trace_cons_2_snoc {from mid to} 
    (step : ActionChainStep from mid)
    (trace : ActionChainTrace mid to) :
    exists (trace' : ActionChainTrace from to),
      action_trace_length (trace') = S (action_trace_length trace).
  Proof.
    generalize dependent from.
    remember mid; induction trace; subst.
    - intros.
      exists (snoc clnil step). cbn; auto.
    - intros.
      cbn. 
      specialize_hypotheses.
      destruct (IHtrace) as (trace' & H).
      exists (snoc trace' l). cbn. auto. 
  Qed.

  (* Lemma action_trace_cons_2_snoc {from mid to} :
    ActionChainStep from mid ->
    ActionChainTrace mid to ->
    (exists mid, 
      inhabited (ActionChainTrace from mid) /\
      inhabited (ActionChainStep mid to)).
  Proof.
    intros step trace. (mid & [step] & [trace']).
    remember (S (action_trace_length trace')) as n.
    generalize dependent mid.
    generalize dependent to.
    generalize dependent from.
    induction n. 
    lia. 
    intros * step * length_eq. 

    split.
    {
      remember (action_trace_length trace) as n. 
      generalize dependent to.
      generalize dependent from.
      induction n. 
      - intros * Hlen (mid & [cl'] & [link]). 
        remember from; destruct (trace); subst; cbn in *; try lia.
        (* no_cyclic *)
        admit.
      - intros * Hlen (mid & [cl'] & [link]).
        remember from; destruct trace; subst; cbn in *; try lia. 

      remember from; induction trace; subst.
      - intros (mid & [cl'] & [link]).
        (* exists mid. *)
        admit.
      - intros (mid' & [cl'] & [link]). 
    }
  Abort. *)

  Lemma no_cyclic_origin_action_trace {origin from mid to} :
    reachable_in_action_trace origin from ->
    ActionChainTrace from mid ->
    ActionChainStep mid to ->
    origin.(chain_state_queue) = to.(chain_state_queue) -> 
    False.
  Proof.
    intros reach trace step queue_eq.
    destruct (action_trace_step' trace) as [|(st1 & step1 & trace1 & trace_eq1)].
    {
      destruct trace; cbn in *; try lia. clear H.
      destruct reach as (reach & [action_trace]).
      specialize (no_cyclic_action_trace_strong reach action_trace step); auto. 
    }
    pose reach as reach_from.
    assert (reach1 : reachable_in_action_trace origin st1). 
    eapply reachable_in_action_trace_step; eauto.
    destruct reach as (reach & [action_trace]).
    specialize (queue_from_account origin reach) as from_accs.
    
    destruct_action_chain_step. rewrite_queue.
    pose (snoc trace1 step) as trace_st1_to.
    specialize (action_trace_drop_le reach1 trace_st1_to) as Hle.
    rewrite_queue.
    specialize (emited_acts_from_is_always_contract reach_from queue_prev eval) as from_contracts.
    rewrite drop_from_contract in Hle; auto.
    rewrite <- queue_eq in *.
    rewrite no_drop_from_account in Hle; auto.
    assert (reach_origin : reachable_in_action_trace origin origin).
    eapply reachable_in_action_trace_refl; eauto.
    specialize (action_trace_drop_le reach_origin action_trace) as Hle'.
    rewrite_queue.
    cbn in *. destruct (address_is_contract (act_from act)) eqn:from_contract; cbn in *.
    - rewrite (no_drop_from_account (chain_state_queue to)) in Hle'; eauto.
      assert (length (list_drop_contract_action acts) =  length (chain_state_queue to)).
      lia.

      
      specialize (action_trace_step' action_trace) as
        [|(next & step_next & trace_next_from & Hnext)].
      + (* origin = from *)
        remember origin; destruct action_trace; subst; cbn in *; try lia.
        rewrite_queue. rewrite <- queue_eq in *. cbn. 
        apply Forall_cons_iff in from_accs as (? & ?). 
        rewrite no_drop_from_account in H; auto. cbn in *.
        lia.
      + assert (inhabited (ActionChainTrace next to)) as [trace_next_to].
        eapply action_trace_trans; eauto.
        exact (snoc trace step).
        assert (reach_next : reachable_in_action_trace origin next).
        eapply reachable_in_action_trace_step; eauto.
        specialize (action_trace_drop_le reach_next trace_next_to) as Hst1.
        destruct_action_chain_step.
        specialize (emited_acts_from_is_always_contract reach_origin queue_prev0 eval0)
         as from_contracts'.
        rewrite_queue.
        rewrite drop_from_contract in Hst1; auto.
        rewrite <- queue_eq in *. 
        rewrite no_drop_from_account in Hst1; auto.
        apply Forall_cons_iff in from_accs as (_ & ?).
        rewrite no_drop_from_account in Hst1; auto.
        cbn in *; lia.
    - assert (length (list_drop_contract_action acts) <= length acts).
      apply list_drop_le.
      rewrite no_drop_from_account in Hle'; eauto.
      lia.
  Qed.

  Lemma finish_action_trace_length_eq 
      {origin from1 from2 to1 to2 : ChainState}
      {act} {acts}
      (trace1 : ActionChainTrace from1 to1)
      (trace2 : ActionChainTrace from2 to2) :
    reachable_in_action_trace origin from1 ->
    reachable_in_action_trace origin from2 ->    
    EnvironmentEquiv from1 from2 ->
    from1.(chain_state_queue) = from2.(chain_state_queue) ->
    origin.(chain_state_queue) = act :: acts ->
    to1.(chain_state_queue) = acts ->
    to2.(chain_state_queue) = acts ->
    action_trace_length' trace1 = action_trace_length' trace2.
  Proof.
    remember (action_trace_length' trace1) as n.
    generalize dependent to2.
    generalize dependent from2.
    generalize dependent to1.
    generalize dependent from1.
    induction n. 
    {
      intros * Hlen * reach1 reach2 env_eq queue queue_origin queue_to1 queue_to2.
      remember from1; destruct trace1; subst; cbn in *; try lia.
      assert (reachable from2).
      {
        assert (inhabited (ChainStep origin from2)) as [step].
        destruct reach2 as (? & [?]).
        constructor.
        eapply (step_action); eauto.
        destruct reach1; auto.
        unfold reachable. destruct H as [trace]. constructor.
        exact (snoc trace step).
      }
      remember from2; destruct trace2; subst; cbn; auto.
      assert (reach2_at : reachable_in_action_trace from2 from2).
      apply reachable_in_action_trace_refl; auto.
      destruct (no_cyclic_origin_action_trace reach2_at trace2 a).
      rewrite_queue. auto.
    }
    intros * Hlen * reach1 reach2 env_eq queue queue_origin queue_to1 queue_to2.
    specialize (action_trace_step' trace1) as [|(mid1 & step1 & trace1' & trace_eq1)].
    {
      destruct trace1; cbn in *; try lia.
    }
    specialize (action_trace_step' trace2) as [|(mid2 & step2 & trace2' & trace_eq2)].
    {
      remember from2; destruct trace2; subst; cbn in *; try lia. clear H.
      rewrite_queue.
      assert (reach1' : reachable from1).
      {
        assert (inhabited (ChainStep origin from1)) as [step].
        destruct reach1 as (? & [?]).
        constructor.
        eapply (step_action); eauto.
        destruct reach1; auto.
        unfold reachable. destruct H as [trace]. constructor.
        exact (snoc trace step).
      }
      specialize (action_trace_cons_2_snoc step1 trace1') as (trace1'' & Htrace1).
      remember from1; destruct trace1'';subst; cbn in *; try lia. 
      destruct (no_cyclic_action_trace_strong reach1' trace1'' a); auto.      
      (* no_cyclic_in_action_trace *)
    }
    subst.
    unfold action_trace_length' in *. 
    repeat rewrite clist_length_app in *.
    cbn in *. 
    specialize (IHn mid1 to1 trace1' ltac:(lia) mid2 to2 trace2').
    specialize (action_step_determin step1 step2 reach1) 
      as (env_eq_mid & queue_eq_mid); auto.
    rewrite IHn; auto.
    apply (reachable_in_action_trace_step reach1); auto.
    apply (reachable_in_action_trace_step reach2); auto.
  Qed.

  Lemma action_trace_finish_equiv 
      {from to1 to2 : ChainState}
      act :
    ActionChainTrace from to1 ->
    ActionChainTrace from to2 ->
    reachable from ->
    from.(chain_state_queue) = act :: to1.(chain_state_queue) ->
    to1.(chain_state_queue) =  to2.(chain_state_queue) ->
    EnvironmentEquiv to1 to2.
  Proof.
    intros trace1 trace2 reach queue queue_to.
    assert (reach_at : reachable_in_action_trace from from) by (apply reachable_in_action_trace_refl; auto).
    specialize (finish_action_trace_length_eq trace1 trace2 reach_at reach_at
      ltac:(reflexivity) ltac:(auto) queue) as Htrace; auto.
    specialize_hypotheses.
    eapply action_trace_equiv_length_iff' in Htrace; auto.
    inversion Htrace; subst; try solve_list_contra; auto.
  Qed.

  Definition reachable_action_trace st := 
    exists from, reachable from /\ inhabited (ActionChainTrace from st). 

  Lemma reachable_action_trace_reahcable_in_action_trace_iff {st} :
    reachable_action_trace st <->
    exists from, reachable_in_action_trace from st. 
  Proof.
    split.
    - intros (from & reach & trace). exists from. split; auto.
    - intros (from & reach & trace). exists from. split; auto.
  Qed.

  Lemma reachable_action_trace_trace {from to} :
    reachable_action_trace from ->
    ActionChainTrace from to ->
    reachable_action_trace to. 
  Proof.
    intros (origin & reach & [trace]) trace'.
    exists origin. split; auto. eapply action_trace_trans; eauto.
  Qed.

  
  Lemma action_step_determin' {prev1 prev2 next1 next2} : 
    ActionChainStep prev1 next1 ->
    ActionChainStep prev2 next2 ->
    reachable_action_trace prev1 ->
    reachable_action_trace prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * step1 step2 (origin1 & reach1 & [action_trace1]) (origin2 & reach2 & [action_trace2])
      env_eq queue_eq.  
    repeat destruct_action_chain_step. 
    rewrite_queue. inversion_subst queue_prev0.
    destruct_action_eval; destruct_action_eval; subst act0; cbn in *; 
      try repeat rewrite_environment_equiv; try congruence.
    - (* transfer *)
      subst; cbn in *. split. 2: rewrite_queue; auto.
      inversion act_eq; subst.
      reflexivity. 
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion_subst act_eq.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto. 
      congruence.
    - (* deploy *)
      inversion_subst act_eq. cbn in *. split; auto.
      pose (build_act limit origin from_addr (act_deploy amount wc setup)) as act.
      assert (ActionEvaluation prev2 act next1 []) as eval1.
      { eapply (eval_deploy limit origin from_addr to_addr0);
         eauto. }
      assert (ActionEvaluation prev2 act next2 []) as eval2.
      { eapply (eval_deploy limit origin from_addr to_addr); 
         eauto. }
      specialize (deploy_address_deterministic eval1 eval2 env_eq1 env_eq0) as addr_eq; subst.
      rewrite init_some in init_some0. inversion_subst init_some0. 
      reflexivity.
    - destruct msg; congruence.
    - (* contra *)
      inversion act_eq; subst.
      destruct msg; try congruence. inversion H3. subst.
      assert (address_is_contract to_addr = true). 
      eapply contract_addr_format_in_action_trace; eauto.
      congruence.
    - destruct msg; congruence.
    - destruct msg0; destruct msg; try congruence.
      + 
        inversion act_eq; subst; clear act_eq ; cbn in *.
        rewrite deployed0 in *. inversion deployed; subst; clear deployed.
        rewrite deployed_state0 in *. inversion deployed_state; subst; clear deployed_state.
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue. auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
      + 
        inversion_subst act_eq; cbn in *.
        rewrite deployed0 in *. inversion_subst deployed.
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb to_addr from_addr); cbn in *.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
        * rewrite receive_some0 in *. inversion_subst receive_some.
          split.
          reflexivity. rewrite_queue; auto.
  Qed.

  Ltac destruct_action_trace_head :=
    match goal with
    | trace : ActionChainTrace ?from ?to |- _ =>
      destruct (action_trace_step' trace) 
        as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
      ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
    | trace : ChainedList ChainState ActionChainStep ?from ?to |- _ =>
      destruct (action_trace_step' trace) 
        as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
      ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
    end.

  Lemma action_step_some :
    forall (prev1 prev2 next1 : ChainState),
      reachable_action_trace prev1 ->
      reachable_action_trace prev2 ->
      ActionChainStep prev1 next1 ->
      EnvironmentEquiv prev1 prev2 ->
      prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
      (exists (next2 : ChainState),
        EnvironmentEquiv next1 next2 /\
        next1.(chain_state_queue) = next2.(chain_state_queue) /\
        inhabited (ActionChainStep prev2 next2)).
  Proof.
    intros * reach_at1 reach_at2 step env_eq queue_eq.
    destruct_action_chain_step; destruct_action_eval.
    - (* transfer *)
      rewrite_environment_equiv;
      rewrite_queue; subst; cbn in *.
      pose (build_chain_state (transfer_balance from_addr to_addr amount prev2) acts) as next2.
      exists next2.
      split; auto. split; auto.
      assert (inhabited (ActionEvaluation prev2
        {|  act_limit := limit;
            act_origin := origin;
            act_from := from_addr;
            act_body := act_transfer to_addr amount |}
        (transfer_balance from_addr to_addr amount prev2) [])) as [eval].
      { constructor. eapply eval_transfer; eauto. reflexivity. }
      constructor. eapply action_step_action; eauto.
    - (* deploy *)
      rewrite_environment_equiv;
      rewrite_queue; subst; cbn in *.
      pose (build_chain_state (set_contract_state to_addr state
               (add_contract to_addr wc
                  (transfer_balance from_addr to_addr amount prev2))) acts) as next2.
      exists next2.
      split; auto. split; auto.
      assert (inhabited (ActionEvaluation prev2
        {| act_limit := limit;
           act_origin := origin;
           act_from := from_addr;
           act_body := act_deploy amount wc setup |}
        (set_contract_state to_addr state
               (add_contract to_addr wc
                  (transfer_balance from_addr to_addr amount prev2))) [])) as [eval].
      { constructor. eapply eval_deploy; eauto. reflexivity. }
      constructor. eapply action_step_action; eauto.      
    - (* call *)
      rewrite_environment_equiv.
      pose (build_chain_state 
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev2)) 
        ( map (build_act (limit - 1) origin to_addr) resp_acts ++ acts)) as next2.
      exists next2.
      split; auto. split. subst; rewrite_queue; auto.
      assert (inhabited (ActionEvaluation prev2
        {| act_limit := limit;
           act_origin := origin;
           act_from := from_addr;
           act_body :=
            match msg with
            | Some msg => act_call to_addr amount msg
            | None => act_transfer to_addr amount
            end |}
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev2))
        (map (build_act (limit - 1) origin to_addr) resp_acts))) as [eval].
      { constructor. eapply eval_call; eauto. rewrite_environment_equiv. apply receive_some. reflexivity. }
      constructor. rewrite_queue. 
      eapply action_step_action; eauto; rewrite_queue; subst. auto.      
  Qed. 

  
  Lemma action_trace_some : 
    forall 
        (from1 from2 to1 : ChainState)
        (trace1 : ActionChainTrace from1 to1),
      reachable_action_trace from1 ->
      reachable_action_trace from2 ->
      EnvironmentEquiv from1 from2 ->
      from1.(chain_state_queue) = from2.(chain_state_queue) ->
      (exists (to2 : ChainState) (trace2 : ActionChainTrace from2 to2),
        EnvironmentEquiv to1 to2 /\
        to1.(chain_state_queue) = to2.(chain_state_queue) /\
        action_trace_length trace1 = action_trace_length trace2 ).
  Proof.
    intros * reach_at1 reach_at2 env_eq queue_eq.
    (* intros * (origin1 & reach_th1) (origin2 & reach_th2) env_eq queue_eq. *)
    induction (trace1) as [|from1 mid1 to1 action_trace1' IHtrace1 step1]; cbn in *; subst.
    {
      (* clnil *)
      exists from2, clnil. split; auto. 
    }
    specialize_hypotheses. 
    destruct IHtrace1 as (mid2 & action_trace2' & env_eq_mid & queue_eq_mid & Hlen).
    assert (reach_at1' : reachable_action_trace mid1).
    { eapply (reachable_action_trace_trace reach_at1); eauto. }
    assert (reach_at2' : reachable_action_trace mid2).
    { eapply (reachable_action_trace_trace reach_at2); eauto. }
    specialize (action_step_some mid1 mid2 to1)
      as (to2 & env_eq_to & queue_eq_to & [step2]); auto.
    exists to2, (snoc action_trace2' step2). cbn. 
    split; auto.  
  Qed.

  Lemma action_trace_finish_equiv_strong
      {from1 from2 to1 to2 : ChainState} {act} :
    ActionChainTrace from1 to1 ->
    ActionChainTrace from2 to2 ->
    reachable from1 ->
    reachable from2 ->    
    EnvironmentEquiv from1 from2 ->
    from1.(chain_state_queue) = act :: to1.(chain_state_queue) ->
    from1.(chain_state_queue) = from2.(chain_state_queue) ->
    to1.(chain_state_queue) =  to2.(chain_state_queue) ->
    EnvironmentEquiv to1 to2.
  Proof.
    enough (P:forall (origin1 origin2 from1 from2 to1 to2 : ChainState) act,
      ActionChainTrace from1 to1 ->
      ActionChainTrace from2 to2 ->
      reachable_in_action_trace origin1 from1 ->
      reachable_in_action_trace origin2 from2 ->    
      EnvironmentEquiv origin1 origin2 ->
      origin1.(chain_state_queue) = act :: to1.(chain_state_queue) ->
      origin1.(chain_state_queue) = origin2.(chain_state_queue) ->
      EnvironmentEquiv from1 from2 ->
      from1.(chain_state_queue) = from2.(chain_state_queue) ->
      to1.(chain_state_queue) =  to2.(chain_state_queue) ->
      EnvironmentEquiv to1 to2
    ).
    { 
      intros.
      apply (P from1 from2 from1 from2 to1 to2 act); auto.
      all:apply reachable_in_action_trace_refl; auto. 
    }
    clear from1 from2 to1 to2 act.
    intros * trace1.
    remember (action_trace_length' trace1) as n.
    generalize dependent to2.
    generalize dependent from2.
    generalize dependent to1.
    generalize dependent from1.
    induction n. 
    {
      intros * Hlen * trace2 reach1 reach2 env_eq queue queue_origin env_eq_from queue_from queue_to1.
      remember from1; destruct trace1; subst; cbn in *; try lia.
      rewrite_queue.
      assert (reachable from2).
      {
        assert (inhabited (ChainStep origin2 from2)) as [step].
        destruct reach2 as (? & [?]).
        constructor.
        eapply (step_action); eauto. rewrite_queue. auto.
        destruct reach2; auto.
        unfold reachable. destruct H as [trace]. constructor.
        exact (snoc trace step).
      }
      remember from2; destruct trace2; subst; cbn; auto.
      assert (reach2_at : reachable_in_action_trace from2 from2).
      apply reachable_in_action_trace_refl; auto.
      destruct (no_cyclic_origin_action_trace reach2_at trace2 a).
      rewrite_queue. auto.
    }
    intros * Hlen * trace2 reach1 reach2 env_eq queue queue_origin env_eq_from queue_from queue_to1.
    specialize (action_trace_step' trace1) as [|(mid1 & step1 & trace1' & trace_eq1)].
    {
      destruct trace1; cbn in *; lia.
    }
    specialize (action_trace_step' trace2) as [|(mid2 & step2 & trace2' & trace_eq2)].
    {
      remember from2; destruct trace2; subst; cbn in *; try lia. clear H.
      rewrite_queue.
      assert (reach1' : reachable from1).
      {
        assert (inhabited (ChainStep origin1 from1)) as [step].
        destruct reach1 as (? & [?]).
        constructor.
        eapply (step_action); eauto.
        destruct reach1; auto.
        unfold reachable. destruct H as [trace]. constructor.
        exact (snoc trace step).
      }
      specialize (action_trace_cons_2_snoc step1 trace1') as (trace1'' & Htrace1).
      remember from1; destruct trace1'';subst; cbn in *; try lia. 
      destruct (no_cyclic_action_trace_strong reach1' trace1'' a); auto. 
      rewrite_queue. auto.     
    }
    subst.
    unfold action_trace_length' in *. 
    repeat rewrite clist_length_app in *.
    cbn in *. 
    specialize (IHn mid1 to1 trace1' ltac:(lia) mid2 to2 trace2').
    specialize (action_step_determin' step1 step2) 
      as (env_eq_mid & queue_eq_mid); auto.
    apply reachable_action_trace_reahcable_in_action_trace_iff; exists origin1; auto.
    apply reachable_action_trace_reahcable_in_action_trace_iff; exists origin2; auto.
    rewrite IHn; auto. reflexivity.
    apply (reachable_in_action_trace_step reach1); auto.
    apply (reachable_in_action_trace_step reach2); auto.
  Qed.



  Definition trace_length {from to} : ChainTrace from to -> nat := clist_length.

  Lemma trace_head_pattern {from to}
      (trace : ChainTrace from to) :
    trace_length trace = 0 \/
    exists mid (step : ChainStep from mid) (trace' : ChainTrace mid to),
      clist_app (snoc clnil step) trace' = trace.
  Proof.
    induction trace. 
    - (* clnil *)
      left; auto.
    - (* snoc *)
      destruct IHtrace as [IH | IH].
      + remember from; destruct trace; cbn in *; try lia. 
        right. exists to, l, clnil. cbn. auto.  
      + destruct IH as (from' & step & trace' & Htrace).
        right.
        exists from', step, (snoc trace' l).
        cbn in *.
        rewrite Htrace.
        auto.
  Qed.

  Lemma chain_step_no_refl {st st': ChainState} :  
    ChainStep st st' -> 
    st.(chain_height) = st'.(chain_height) ->
    st.(chain_state_queue) = st'.(chain_state_queue) ->
    False.
  Proof.
    intros step height_eq queue_eq.
    destruct_chain_step. 
    - destruct valid_header. rewrite_environment_equiv; cbn in *. lia.
    - rewrite_queue. solve_list_contra.
    - rewrite_queue. solve_list_contra. 
  Qed.

  Lemma chain_height_le {from to} :
    ChainTrace from to ->
    from.(chain_height) <= to.(chain_height).
  Proof.
    intro trace. trace_induction.
    - destruct valid_header. rewrite_environment_equiv. cbn. lia.
    - action_trace_induction_intermidiate.
      destruct_action_eval; rewrite_environment_equiv; cbn; lia.
    - rewrite_environment_equiv. auto.
  Qed.

  Lemma action_trace_chain_height_invariant {from to} :
    ActionChainTrace from to ->
    from.(chain_height) = to.(chain_height).
  Proof.
    intro action_trace. action_trace_induction.
    destruct_action_eval; rewrite_environment_equiv; cbn; auto.
  Qed.

  Lemma chain_step_determin {prev1 prev2 next1 next2} : 
    ChainStep prev1 next1 ->
    ChainStep prev2 next2 ->
    reachable prev1 ->
    reachable prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) <> [] ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    prev1.(chain_height) = next1.(chain_height) /\ 
    prev2.(chain_height) = next2.(chain_height) /\
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * step1 step2 reach1 reach2
      env_eq no_nil queue_eq.
    destruct_chain_step; destruct_chain_step; try congruence.  
    repeat destruct_action_chain_step. 
    rewrite_queue. inversion_subst queue_prev0.
    - (* valid, valid *) (* determin *)
      split. eapply (action_trace_chain_height_invariant); auto.
      split. eapply (action_trace_chain_height_invariant); auto.
      split; auto.
      eapply action_trace_finish_equiv_strong; eauto.
      all : rewrite_queue; auto.
    - (* invalid, valid *) (* contra *)
      specialize (action_trace_some prev2 prev1 next2)
        as (next1' & action_trace1 & _ & queue_eq1 & _); auto.
      exists prev2. split; auto. repeat constructor.
      exists prev1. split; auto. repeat constructor.
      rewrite_environment_equiv. reflexivity.
      destruct (no_action_trace next1'); auto. rewrite_queue. 
      inversion queue_prev0. auto.
    - (* valid, invalid *)
      specialize (action_trace_some prev1 prev2 next1)
        as (next2' & action_trace2 & _ & queue_eq2 & _); auto.
      exists prev1. split; auto. repeat constructor.
      exists prev2. split; auto. repeat constructor.
      destruct (no_action_trace next2'); auto. rewrite_queue. 
      inversion queue_prev0. auto.
    - (* invalid, invalid *)
      repeat rewrite_environment_equiv. rewrite_queue. inversion queue_prev0.
      repeat split; auto.
      Unshelve. auto. auto.
  Qed.

  Lemma cyclic_trace_eq {from to} :
    ChainTrace from to ->
    from.(chain_height) = to.(chain_height) ->
    length from.(chain_state_queue) <= length to.(chain_state_queue) -> 
    from = to.
  Proof.
    intros trace Hheight Hlen.
    trace_induction.
    - specialize (chain_height_le trace) as Hheight'.
      rewrite_environment_equiv. cbn in *. destruct valid_header.
      lia.
    - rewrite_queue.
      assert (H: chain_height mid = chain_height to)
        by (apply action_trace_chain_height_invariant; auto).
      cbn in *. rewrite H in *. specialize (IH ltac:(auto) ltac:(lia)).
      subst.
      rewrite_queue. cbn in *; lia.
    - rewrite_queue. cbn in *. rewrite_environment_equiv.
      specialize (IH ltac:(auto) ltac:(lia)). subst.
      rewrite_queue. cbn in *; lia.
  Qed. 

  Lemma trace_head_pattern_strong {from to}
      (trace : ChainTrace from to) :
    trace_length trace = 0 \/
    exists mid (step : ChainStep from mid) (trace' : ChainTrace mid to),
      clist_app (snoc clnil step) trace' = trace.
  Proof.
    induction trace. 
    - (* clnil *)
      left; auto.
    - (* snoc *)
      destruct IHtrace as [IH | IH].
      + remember from; destruct trace; cbn in *; try lia. 
        right. exists to, l, clnil. cbn. auto.  
      + destruct IH as (from' & step & trace' & Htrace).
        right.
        exists from', step, (snoc trace' l).
        cbn in *.
        rewrite Htrace.
        auto.
  Qed.

  Ltac destruct_trace_head :=
    match goal with
    | trace : ChainTrace ?from ?to |- _ =>
      destruct (trace_head_pattern_strong trace) 
        as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
      ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
    | trace : ChainedList ChainState ChainStep ?from ?to |- _ =>
      destruct (trace_head_pattern_strong trace) 
        as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
      ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
    end.

  Lemma chain_trace_trans {from mid to} :
    ChainTrace from mid ->
    ChainTrace mid to ->
    inhabited (ChainTrace from to).
  Proof.
    intros trace1 trace2.
    generalize dependent from.
    induction trace2.
    constructor; auto.
    intros * trace1. specialize (IHtrace2 from0 trace1) as [trace].
    constructor. apply (snoc trace l).
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

  Lemma trace_gt_lt {from to} (trace : ChainTrace from to) :
    0 < trace_length trace ->
    chain_height from < chain_height to \/
    length (chain_state_queue from) > length (chain_state_queue to).
  Proof.
    intros H.
    (* trace_induction. *)
    remember from; induction trace; subst; cbn in *; try lia.
    destruct_trace_head.
    - (* step *)
      clear IHtrace H.
      destruct_chain_step.
      + left. destruct valid_header. rewrite_environment_equiv. cbn. lia.
      + right. rewrite_queue. cbn; lia.
      + right. rewrite_queue. cbn; lia. 
    - 
      subst. unfold trace_length in IHtrace. 
      rewrite clist_length_app in IHtrace. cbn in *.
      assert (inhabited (ChainTrace from to)) as [trace_from_to].
      {
        eapply chain_trace_trans; eauto.
        apply (snoc clnil step).
        apply (snoc trace' l).
      }
      specialize (chain_height_le trace_from_to) as Hheight.
      specialize (trace_step step trace') as [trace_from_mid].
      specialize (IHtrace ltac:(auto) ltac:(lia)) as [IH|IH].
      + left.
        destruct l.
        * rewrite_environment_equiv. cbn. destruct i. lia. 
        * specialize (action_trace_chain_height_invariant a).
          lia. 
        * rewrite_environment_equiv. lia.
      + 
        clear H step.
        destruct_chain_step.
        * (* contra *) 
          specialize (chain_height_le trace_from_mid) as Hheight'.
          destruct valid_header. rewrite_environment_equiv. cbn in *.
          lia. 
        * right; rewrite_queue; cbn in *; lia.
        * right; rewrite_queue; cbn in *; lia.
  Qed.

  Lemma trace_determin_until_add_block 
      {from to1 to2} :
    reachable from ->
    ChainTrace from to1 ->
    ChainTrace from to2 ->    
    from.(chain_height) = to1.(chain_height) ->
    from.(chain_height) = to2.(chain_height) ->
    length to1.(chain_state_queue) = length to2.(chain_state_queue) ->
    EnvironmentEquiv to1 to2 /\
    to1.(chain_state_queue) = to2.(chain_state_queue).
  Proof.
    enough (P: forall from1 from2 to1 to2,
      ChainTrace from1 to1 ->
      ChainTrace from2 to2 ->
      reachable from1 ->
      reachable from2 ->    
      EnvironmentEquiv from1 from2 ->
      from1.(chain_state_queue) = from2.(chain_state_queue) ->
      from1.(chain_height) = to1.(chain_height) ->
      from2.(chain_height) = to2.(chain_height) ->
      length to1.(chain_state_queue) = length to2.(chain_state_queue) -> (* ? *)
      EnvironmentEquiv to1 to2 /\
      to1.(chain_state_queue) = to2.(chain_state_queue)        
    ).
    {
      (* enough *)
      intros. apply (P from from to1 to2); auto. reflexivity.
    }
    clear from to1 to2.
    intros * trace1.
    remember (trace_length trace1) as n. 
    generalize dependent trace1.
    generalize dependent to2.
    generalize dependent to1.
    generalize dependent from2.
    generalize dependent from1.
    induction n.
    {
      intros * Hlen *.
      destruct trace1; cbn in *; try lia.
      clear Hlen.
      intros trace2.
      destruct_trace_head.
      - 
        split; auto. 
      - (* contra *)
        specialize (trace_gt_lt trace2) as [contra|contra].
        subst. unfold trace_length. rewrite clist_length_app. cbn. lia. 
        + intros. lia. 
        + intros. rewrite_queue. lia. 
    }
    
    intros * Hlen.
    destruct_trace_head; cbn in *; try lia.
    intros trace2 reach1 reach2 env_eq queue_eq.
    destruct_trace_head.
    {
      (* trace2 = clnil *)
      intros height_eq1 _ Hlen_to.
      specialize (trace_step step trace') as [trace].
      destruct (cyclic_trace_eq trace) in *; auto.
      rewrite_queue. lia.
    }
    intros height1 height2 queue_len.
    enough (Hmid :
      from1.(chain_height) = mid.(chain_height) /\ 
      from2.(chain_height) = mid0.(chain_height) /\
      EnvironmentEquiv mid mid0 /\
      mid.(chain_state_queue) = mid0.(chain_state_queue)).
    { 
      destruct Hmid 
        as (height_mid & height_mid0 & env_eq_mid & queue_eq_mid).
      (* intros height1 height2 queue_eq_to.  *)
      apply (IHn mid mid0 to1 to2 trace'); auto.
      subst. unfold trace_length in *.
      rewrite clist_length_app in *. cbn in *. lia.
      eapply (reachable_step from1); eauto.
      eapply (reachable_step from2); eauto.
      rewrite <- height1, height_mid; auto.
      rewrite <- height2, height_mid0; auto.
    }
    eapply chain_step_determin; auto.
    
    unfold not. intro queue_from.
    clear trace_eq0 step0.
    destruct_chain_step; try congruence.
    specialize (chain_height_le trace') as Hheight_mid.
    destruct valid_header.
    repeat rewrite_environment_equiv. cbn in *. rewrite valid_height in *.
    rewrite <- height1 in *. rewrite_environment_equiv. lia. 
  Qed.

  (* 20260205 *)
  Inductive ChainTraceEquiv
    : (forall {from1 from2 to1 to2}, 
        ChainTrace from1 to1 -> ChainTrace from2 to2 -> Prop) :=
  | equiv_clnil {p1 p2 : ChainState} : 
      ChainTraceEquiv (@clnil ChainState ChainStep p1) 
                            (@clnil ChainState ChainStep p2)
  | equiv_snoc {from1 from2 mid1 mid2 to1 to2 : ChainState} 
                  {trace1 : ChainTrace from1 mid1} 
                  {trace2 : ChainTrace from2 mid2} 
                  {step1 : ChainStep mid1 to1} 
                  {step2 : ChainStep mid2 to2} :
      EnvironmentEquiv to1 to2 ->
      to1.(chain_state_queue) = to2.(chain_state_queue) ->
      ChainTraceEquiv trace1 trace2 ->
      ChainTraceEquiv (snoc trace1 step1) (snoc trace2 step2).

  Lemma reachable_through_reachable_strong : forall from to (reach : ChainTrace empty_state from),
    reachable_through from to -> 
    exists (trace : ChainTrace from to) (reach' : ChainTrace empty_state to),
      clist_app reach trace = reach'.
  Proof.
    intros * [_ [trace_to]].
    exists trace_to, (clist_app reach trace_to). auto.
  Qed.

  Lemma deployment_info_invariant 
       Setup `{Serializable Setup} (depinfo : DeploymentInfo Setup)
       caddr from to (trace : ChainTrace empty_state from) :
    reachable_through from to ->
    deployment_info Setup trace caddr = Some depinfo ->
    exists (trace' : ChainTrace empty_state to),
      deployment_info Setup trace' caddr = Some depinfo.
  Proof.
     
  Abort.

  Lemma reachable_through_equiv {st st'} 
                                (reach  : ChainTrace empty_state st)
                                (trace  : ChainTrace st st')
                                (reach' : ChainTrace empty_state st') :
    ChainTraceEquiv (clist_app reach trace) reach'.
  Proof.
  Abort.
  
End ChainTraceProperty.