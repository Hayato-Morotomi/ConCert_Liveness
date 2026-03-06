










From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import MyBuildUtils.
From Stdlib Require Import ZArith_base.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Streams.
From Stdlib Require Import Basics.
From Stdlib Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Monad.
From ConCert.Examples.Wip.General Require Import Agreement.
From ConCert.Examples.Wip.Ppl2026 Require Import Liveness.

Section DomainSpecificConstructs.
  Context {BaseTypes : ChainBase}.

  Context {Setup Msg State Error : Type}.
  Context `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}.

  Open Scope Z_scope.

  Local Ltac rewrite_queue :=
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *
      end.

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

  
  Definition valid_token_ctx (st : ChainState) ctx : Prop :=
      (0 < ctx.(ctx_limit))%nat /\
      (0 <= ctx.(ctx_amount))%Z /\
      (env_account_balances st ctx.(ctx_from) >= ctx.(ctx_amount))%Z.

  Lemma hd_error_iff {A : Type} : forall (x : A) (l:list A),
    hd_error l = Some x <-> exists l', l = x :: l'.
  Proof.
    intros *. split.
    -
      destruct l; cbn in *; try congruence.
      exists l. inversion H3; auto. 
    - intros (l' & ?).
      subst; auto. 
  Qed.

  












  Definition pre (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) (ctx : ContractCallContext)
                  : Prop :=
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    reachable_action_trace st /\
    List.hd_error st.(chain_state_queue) = 
      Some (build_act limit origin_addr from_addr
        (match msg with
            | None => act_transfer caddr amount
            | Some m => act_call caddr amount ((@serialize Msg _) m)
          end)) /\
    valid_token_ctx st ctx /\
    env_contracts st caddr = Some (contract : WeakContract) /\
    exists (cstate : State) (new_cstate : State) (new_acts : list ActionBody),
      contract_state st caddr = Some cstate /\ 
      receive contract 
          (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) st) 
          (ctx<|ctx_contract_balance := 
              if (address_eqb from_addr caddr)
                  then (env_account_balances st caddr)
                  else ((env_account_balances st caddr) + amount)%Z|>)
          cstate msg
        = Ok (new_cstate, new_acts).

  
  Lemma pre_sound : forall 
        (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext) 
                 cstate new_cstate new_acts,
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    ActionChainStep prev next ->
    contract_state prev caddr = Some cstate ->
    receive contract 
        (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) prev) 
        (ctx <|ctx_contract_balance := 
              if (address_eqb from_addr caddr)
                  then (env_account_balances prev caddr)
                  else ((env_account_balances prev caddr) + amount)%Z|>)
        cstate msg 
      = Ok (new_cstate, new_acts) ->
    pre contract msg prev ctx -> 
    reachable_action_trace next
    /\ contract_state next caddr = Some new_cstate
    /\ chain_state_queue next = 
        (List.map (build_act (limit - 1) origin_addr caddr) new_acts) 
        ++ List.tl prev.(chain_state_queue)
    /\ EnvironmentEquiv
        next
        (set_contract_state caddr (serialize new_cstate) 
          (transfer_balance from_addr caddr amount prev)).
  Proof.
      intros * step deployed_cstate' receive_some'
        (reach & queue & (Hlimit & Hammount & Henough) & deployed
          & cstate & new_cstate & new_acts & deployed_cstate & receive_some).
      apply hd_error_iff in queue as (acts & queue). 
      apply reachable_action_trace_reahcable_in_action_trace_iff in reach as (from & reach).
      split.
      apply reachable_action_trace_reahcable_in_action_trace_iff. exists from. eapply reachable_in_action_trace_step; eauto.
      specialize (contract_addr_format_action_trace caddr contract reach deployed) as from_contract.
      subst limit origin_addr from_addr caddr amount.
      rewrite deployed_cstate in *. inversion_subst deployed_cstate'.
      rewrite receive_some in *. inversion_subst receive_some'.
      destruct msg.
      - (* evaluate_action' *) 
        destruct_action_chain_step.
        destruct_action_eval; try congruence; rewrite_queue; subst.
        inversion_subst queue_prev.
        destruct msg; try congruence. inversion_subst H7.
        rewrite deployed in *. inversion_subst deployed0.
        cbn in deployed_cstate. rewrite deployed_state in *.
        eapply wc_receive_to_receive' in receive_some; eauto.
        repeat rewrite_environment_equiv.
        simpl in *. rewrite address_eq_refl in receive_some0.
        rewrite address_eq_sym in receive_some.
        replace ((- ctx_amount ctx +
                                     (ctx_amount ctx +
                                      env_account_balances prev
                                        (ctx_contract_address ctx)))%Z)
          with (env_account_balances prev (ctx_contract_address ctx)) 
          in receive_some0 by lia.
        replace ((ctx_amount ctx +
                                     env_account_balances prev
                                       (ctx_contract_address ctx))%Z)
          with ((env_account_balances prev
                                      (ctx_contract_address ctx) + 
                                    ctx_amount ctx)%Z) 
          in receive_some0 by lia.
        unfold setter_from_getter_ContractCallContext_ctx_contract_balance,
          set_ContractCallContext_ctx_contract_balance in receive_some.
        rewrite receive_some in receive_some0. inversion_subst receive_some0.
        cbn. rewrite address_eq_refl, deserialize_serialize.
        repeat split; auto.  
      - (* eval_call transfer *)
        destruct_action_chain_step.
        destruct_action_eval; try congruence; rewrite_queue; subst.
        inversion_subst queue_prev.
        destruct msg; try congruence. inversion_subst H7.
        rewrite deployed in *. inversion_subst deployed0.
        cbn in deployed_cstate. rewrite deployed_state in *.
        eapply wc_receive_to_receive_None in receive_some; eauto.
        repeat rewrite_environment_equiv.
        simpl in *. rewrite address_eq_refl in receive_some0.
        rewrite address_eq_sym in receive_some.
        replace ((- ctx_amount ctx +
                                     (ctx_amount ctx +
                                      env_account_balances prev
                                        (ctx_contract_address ctx)))%Z)
          with (env_account_balances prev (ctx_contract_address ctx)) 
          in receive_some0 by lia.
        replace ((ctx_amount ctx +
                                     env_account_balances prev
                                       (ctx_contract_address ctx))%Z)
          with ((env_account_balances prev
                                      (ctx_contract_address ctx) + 
                                    ctx_amount ctx)%Z) 
          in receive_some0 by lia.
        unfold setter_from_getter_ContractCallContext_ctx_contract_balance,
          set_ContractCallContext_ctx_contract_balance in receive_some.
        rewrite receive_some in receive_some0. inversion_subst receive_some0.
        cbn. rewrite address_eq_refl, deserialize_serialize.
        repeat split; auto.
  Qed.
  
  Lemma pre_correct (contract : Contract Setup Msg State Error) 
                    (msg : option Msg)
                    (prev : ChainState) 
                    (ctx : ContractCallContext)  :
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    pre contract msg prev ctx 
    <->
    reachable_action_trace prev /\
    List.hd_error prev.(chain_state_queue) = 
      Some (build_act limit origin_addr from_addr
        (match msg with
          | None => act_transfer caddr amount
          | Some m => act_call caddr amount ((@serialize Msg _) m)
        end)) /\
    env_contracts prev caddr = Some (contract : WeakContract) /\
    exists (next : ChainState) (cstate new_cstate : State) (new_acts : list ActionBody),
      inhabited (ActionChainStep prev next)
      /\ contract_state prev caddr = Some cstate
      /\ receive contract 
          (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) prev) 
          (ctx <|ctx_contract_balance := 
                if (address_eqb from_addr caddr)
                    then (env_account_balances prev caddr)
                    else ((env_account_balances prev caddr) + amount)%Z|>)
          cstate msg 
        = Ok (new_cstate, new_acts)
    
      /\ contract_state next caddr = Some new_cstate
      /\ chain_state_queue next = 
          (List.map (build_act (limit - 1) origin_addr caddr) new_acts) 
          ++ List.tl prev.(chain_state_queue)
      /\ EnvironmentEquiv
          next
          (set_contract_state caddr (serialize new_cstate) 
            (transfer_balance from_addr caddr amount prev))
      /\  (* deterministic *)
        (forall next', 
          ActionChainStep prev next' ->
          EnvironmentEquiv next next' /\
          chain_state_queue next = chain_state_queue next'
        ).
  Proof.
    split. 
    {
      (* sound *)
      intros Hpre.
      pose Hpre as Hpre'.
      destruct Hpre' as (reach & queue & (Hlimit & Hammount & Henough) & deployed
          & cstate & new_cstate & new_acts & deployed_cstate & receive_some).
      repeat split; auto. 
      pose (build_chain_state
        ((set_contract_state (ctx_contract_address ctx) (serialize new_cstate)
            (transfer_balance (ctx_from ctx) (ctx_contract_address ctx) (ctx_amount ctx) prev)))
        (List.map
          (build_act (ctx_limit ctx - 1) (ctx_origin ctx) (ctx_contract_address ctx))
          new_acts ++ List.tl (chain_state_queue prev))
      ) as next.
      apply hd_error_iff in queue as (acts & queue).
      exists next, cstate, new_cstate, new_acts.
      assert (inhabited (ActionChainStep prev next)) as step.
      {
        assert (eval : ActionEvaluation prev {|
          act_limit := ctx_limit ctx;
          act_origin := ctx_origin ctx;
          act_from := ctx_from ctx;
          act_body :=
            match msg with
            | Some m =>
                act_call (ctx_contract_address ctx) (ctx_amount ctx) (serialize m)
            | None => act_transfer (ctx_contract_address ctx) (ctx_amount ctx)
            end
        |} next 
        (List.map (build_act (ctx_limit ctx - 1) (ctx_origin ctx) (ctx_contract_address ctx))
          new_acts)).
        { 
          cbn in deployed_cstate.
          destruct (env_contract_states prev (ctx_contract_address ctx)) eqn:Hdeployed_state; try congruence.
          destruct msg eqn:Hmsg.
          - (* Some *)
            eapply wc_receive_to_receive' in receive_some; eauto. 
            eapply eval_call with 
            (amount := ctx_amount ctx) (from_addr := ctx_from ctx) (origin := ctx_origin ctx)
            (prev_state := s) (msg := Some (serialize m)); 
            eauto; try lia.
            + cbn in *. rewrite address_eq_refl.
              replace (- ctx_amount ctx +
                    (ctx_amount ctx +
                     env_account_balances prev (ctx_contract_address ctx))) with
                  (env_account_balances prev (ctx_contract_address ctx)) by lia. 
              rewrite address_eq_sym. rewrite Z.add_comm.
              eapply receive_some.
            + subst next. cbn. reflexivity. 
          - (* None *)
            eapply wc_receive_to_receive_None in receive_some; eauto.
            eapply eval_call with 
            (amount := ctx_amount ctx) (from_addr := ctx_from ctx) (origin := ctx_origin ctx)
            (prev_state := s) (msg := None); 
            eauto; try lia.
            + cbn in *. rewrite address_eq_refl.
              replace (- ctx_amount ctx +
                    (ctx_amount ctx +
                     env_account_balances prev (ctx_contract_address ctx))) with
                  (env_account_balances prev (ctx_contract_address ctx)) by lia. 
              rewrite address_eq_sym. rewrite Z.add_comm.
              eapply receive_some.
            + subst next. cbn. reflexivity.
        } 
        constructor.
        econstructor; eauto. subst next; cbn. rewrite_queue. auto.
      }
      split; auto.
      destruct step as [step]. 
      destruct reach as (origin & reach).
      split; auto. 
      split; auto.  
      specialize (pre_sound contract msg prev next ctx cstate new_cstate new_acts) 
        as (_ & deployed_cstate_new & queue_new & env_eq); auto.
      split; auto. split; auto. split; auto. 
      intros * step'. 
      eapply action_step_weak_deterministic; eauto.
    }
    unfold pre.
    intros (reach & queue & deployed & (next & cstate & new_cstate & new_acts & [step] & deployed_state & receive_some
      & deployed_state_next & queue_new & env_eq & step_determin)). 
    split; auto. 
    destruct_action_chain_step. 
    (* specialize (deployed_state_wc_typed_action_trace deployed_state)
      as (wc & deployed); eauto.  *)
    apply reachable_action_trace_reahcable_in_action_trace_iff in reach as (from & reach_at).
    assert (address_is_contract  (ctx_contract_address ctx) = true) as contract_addr.
    eapply contract_addr_format_action_trace; eauto.
    rewrite_queue. cbn in queue. inversion_subst queue.
    split; auto. 
    destruct_action_eval; inversion_subst act_eq.
    - (* transfer *) (* contra *)
      destruct msg; congruence.
    - (* deploy *)
      destruct msg; congruence. 
    - (* call *)
      destruct msg; destruct msg0; try congruence; inversion_subst H7.
      + (* call *)
        inversion_deployed_contract.
        split. 
        repeat split; lia. 
        split; auto. 
        exists  cstate, new_cstate, new_acts. 
        split; auto. 
      + (* call transfer *)
        inversion_deployed_contract.
        split. 
        repeat split; lia. 
        split; auto. 
        exists  cstate, new_cstate, new_acts. 
        split; auto. 
  Qed.

  












  Definition post (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext) 
                 : Prop :=
    reachable_action_trace prev /\
    inhabited (ActionChainStep prev next) /\
    List.hd_error prev.(chain_state_queue) = 
      Some (build_act ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) 
        (match msg with
          | None => act_transfer ctx.(ctx_contract_address) ctx.(ctx_amount)
          | Some m => act_call ctx.(ctx_contract_address) ctx.(ctx_amount) ((@serialize Msg _) m)
        end)) /\
    env_contracts prev ctx.(ctx_contract_address) = Some (contract : WeakContract).

  Lemma post_correct  : forall
                 (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext),
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    post contract msg prev next ctx ->
    exists cstate new_cstate new_acts,
      env_contracts prev caddr = Some (contract : WeakContract) /\
      contract_state prev caddr = Some cstate /\
      receive contract 
          (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) prev) 
          {| ctx_origin := origin_addr;
              ctx_from := from_addr;
              ctx_contract_address := caddr;
              ctx_contract_balance := if (address_eqb from_addr caddr)
                  then (env_account_balances prev caddr)
                  else ((env_account_balances prev caddr) + amount)%Z;
              ctx_amount := amount;
              ctx_limit := limit
          |}
          cstate msg 
        = Ok (new_cstate, new_acts) /\
      reachable_action_trace next
      /\ contract_state next caddr = Some new_cstate
      /\ chain_state_queue next = 
        (List.map (build_act (limit - 1) origin_addr caddr) new_acts) ++ List.tl prev.(chain_state_queue)
      /\ EnvironmentEquiv
          next
          (set_contract_state caddr (serialize new_cstate) 
            (transfer_balance from_addr caddr amount prev)).
  Proof.
    intros * Hpost.
    destruct Hpost as [reach ([step] & queue & deployed)].
    apply hd_error_iff in queue as (acts & queue).
    apply reachable_action_trace_reahcable_in_action_trace_iff in reach as (from & reach).
    specialize (contract_addr_format_action_trace caddr contract reach deployed) as from_contract.
    assert (reach_at : reachable_action_trace next).
    { apply reachable_action_trace_reahcable_in_action_trace_iff. exists from. eapply reachable_in_action_trace_step; eauto. }
    destruct_action_chain_step.
    subst limit origin_addr from_addr caddr amount.
    destruct msg.    
    - (* some *)
      destruct_action_eval; try congruence; subst.
      rewrite_queue. inversion_subst queue_prev.
      destruct msg; try congruence. inversion_subst H7.
      rewrite deployed in *. inversion_subst deployed0.
      apply wc_receive_strong in receive_some
        as (prev_state_strong & msg_strong & new_state_strong & Hser_cstate & Hser_msg & Hser_cstate_new & receive_some).
      exists prev_state_strong, new_state_strong, resp_acts.
      split; auto. 
      cbn in *.
      rewrite deployed_state. split; auto.
      rewrite_environment_equiv. 
      destruct msg_strong; try congruence. rewrite deserialize_serialize in Hser_msg.
      inversion_subst Hser_msg.
      split; auto.
      {
        simpl in *. rewrite address_eq_refl in receive_some.
        rewrite address_eq_sym in receive_some.
        replace ((- ctx_amount ctx +
                                     (ctx_amount ctx +
                                      env_account_balances prev
                                        (ctx_contract_address ctx)))%Z)
          with (env_account_balances prev (ctx_contract_address ctx)) 
          in receive_some by lia.
        replace ((ctx_amount ctx +
                                     env_account_balances prev
                                       (ctx_contract_address ctx))%Z)
          with ((env_account_balances prev
                                      (ctx_contract_address ctx) + 
                                    ctx_amount ctx)%Z) 
          in receive_some by lia.
        auto.       
      }
      split; auto. cbn. rewrite address_eq_refl, deserialize_serialize. 
      repeat split; auto. 
    - (* eval_call transfer *)
      destruct_action_eval; try congruence; subst.
      rewrite_queue. inversion_subst queue_prev.
      destruct msg; try congruence. inversion_subst H7.
      rewrite deployed in *. inversion_subst deployed0.
      apply wc_receive_strong in receive_some
        as (prev_state_strong & msg_strong & new_state_strong & Hser_cstate & Hser_msg & Hser_cstate_new & receive_some).
      exists prev_state_strong, new_state_strong, resp_acts.
      split; auto. 
      cbn in *.
      rewrite deployed_state. split; auto.
      rewrite_environment_equiv. 
      destruct msg_strong; try congruence. 
      split; auto.
      {
        simpl in *. rewrite address_eq_refl in receive_some.
        rewrite address_eq_sym in receive_some.
        replace ((- ctx_amount ctx +
                                     (ctx_amount ctx +
                                      env_account_balances prev
                                        (ctx_contract_address ctx)))%Z)
          with (env_account_balances prev (ctx_contract_address ctx)) 
          in receive_some by lia.
        replace ((ctx_amount ctx +
                                     env_account_balances prev
                                       (ctx_contract_address ctx))%Z)
          with ((env_account_balances prev
                                      (ctx_contract_address ctx) + 
                                    ctx_amount ctx)%Z) 
          in receive_some by lia.
        auto.       
      }
      split; auto. cbn. rewrite address_eq_refl. 
      subst. rewrite deserialize_serialize.
      repeat split; auto. 
  Qed.

  Lemma pre_post (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext) :
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    pre contract msg prev ctx /\ inhabited (ActionChainStep prev next)
    <->
    post contract msg prev next ctx.
  Proof.
    split. 
    {
      (* pre -> post *) 
      unfold post.
      intros (Hpre & step). pose Hpre as Hpre'.
      destruct Hpre as (reach & queue & (Hlimit & Hammount & Henough) & deployed
          & cstate & new_cstate & new_acts & deployed_cstate & receive_some). 
      split; auto.
    }
    {
      intro Hpost.
      specialize (post_correct contract msg prev next ctx Hpost)
        as (cstate & new_cstate & new_acts & deployed_cstate & receive_some
          & reach_next & deployed_state_next & queue_next & env_eq). 
      unfold pre. 
      destruct Hpost as (reach & step & queue_prev & deployed). 
      split; auto. split; auto. split; auto. split. 
      - destruct step as [step]. 
        destruct_action_chain_step. 
        rewrite_queue. inversion_subst queue_prev.
        destruct_action_eval; subst; inversion_subst act_eq; 
          destruct msg; try congruence; inversion_subst H7; 
          repeat split; try lia; auto; 
          destruct msg0; try congruence; inversion_subst H4; lia. 
      - split; auto. 
        exists cstate, new_cstate, new_acts. 
        repeat split; auto. 
    }
  Qed.   

  


  Definition enabled (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) (ctx : ContractCallContext) :=
    forall acts,
      st.(chain_state_queue) = (build_act ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
        (match msg with
            | None => act_transfer ctx.(ctx_contract_address) ctx.(ctx_amount)
            | Some m => act_call ctx.(ctx_contract_address) ctx.(ctx_amount) ((@serialize Msg _) m)
          end)) 
        :: acts ->
      pre contract msg st ctx.


  
  
  Definition enabled_classic (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) (ctx : ContractCallContext) :=
    pre contract msg st ctx.

  





  Definition enabled_forall (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) : Prop :=
    forall ctx,
      (0 < ctx.(ctx_limit))%nat ->
      (0 <= ctx.(ctx_amount))%Z ->
      (env_account_balances st ctx.(ctx_from) >= ctx.(ctx_amount))%Z ->
      env_contracts st ctx.(ctx_contract_address) = Some (contract : WeakContract) ->
      pre contract msg st ctx.

  Definition enabled_pred (contract : Contract Setup Msg State Error)
                 (c : ChainState -> ChainState -> Prop)
                 (st : ChainState) (ctx : ContractCallContext) :=
    forall prev (acts : list Action),
      ActionChainStep prev st ->
      exists (msg : option Msg),
        enabled contract msg prev ctx /\
        post contract msg prev st ctx /\
        c prev st.
  
  
  Definition prop_transfer from to ammount prev next : Prop :=
    ActionChainStep prev next ->
    env_account_balances next from =  env_account_balances next from - ammount /\
    env_account_balances next to =  env_account_balances next to + ammount. 

  
  Definition own (contract : Contract Setup Msg State Error)
                 (st : ChainState)
                 addr amount : Prop :=
    forall ctx,
      addr = ctx.(ctx_from) ->
      amount = ctx.(ctx_amount) ->
      valid_token_ctx st ctx ->
      pAF  
        (fun bstate =>
         enabled_pred contract (prop_transfer ctx.(ctx_contract_address) addr amount) bstate ctx)
        st.

  



  
















































































































































































































































































  



  (* Definition post (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext) 
                 {acts prev_state new_state new_acts}
                 : Prop :=
    inhabited (ActionChainStep prev next) /\
    env_contracts prev ctx.(ctx_contract_address) = Some (contract : WeakContract) /\
    prev.(chain_state_queue) = (build_act ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) 
      (match msg with
          | None => act_transfer ctx.(ctx_contract_address) ctx.(ctx_amount)
          | Some m => act_call ctx.(ctx_contract_address) ctx.(ctx_amount) ((@serialize Msg _) m)
        end)) 
      :: acts /\
    contract_state prev ctx.(ctx_contract_address) = Some prev_state /\
    contract.(receive) prev ctx prev_state msg = Ok (new_state, new_acts). *)

End DomainSpecificConstructs.