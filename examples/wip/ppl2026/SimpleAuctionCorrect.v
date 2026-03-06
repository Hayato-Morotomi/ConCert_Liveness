(* SimpleAuctionCorrect *)

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Examples.Wip.General Require Import Blockchain_modify_2.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify_2.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import ChainStreamProperty.
From ConCert.Examples.Wip.General Require Import ContractCommon_modify_2.
From ConCert.Examples.Wip.General Require Import MyBuildUtils.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.
From Coq Require Import Lia.
From Coq Require Import Streams.
From ConCert.Examples.Wip.TemporalLogic Require Import Agreement.
From ConCert.Examples.Wip.TemporalLogic Require Import Liveness.
From ConCert.Execution Require Import Serializable.
From ConCert.Examples.Wip.General Require Import Jonas2024_speclang.
From ConCert.Examples.Wip.SimpleAuction Require Import SimpleAuction.

Section Theories.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.

  
  Ltac inversion_deployed_contract :=
    match goal with
    | [deployed: env_contracts ?env ?caddr = Some _,
       deployed' : env_contracts ?env ?caddr = Some ?wc' |- _] => 
        rewrite deployed in deployed'; inversion_subst deployed'
    | [deployed_state : contract_state ?env ?caddr = Some _,
       deployed_state' : contract_state ?env ?caddr = Some ?cstate' |- _] => 
        rewrite deployed_state in deployed_state'; inversion_subst deployed_state'
    | [deployed_state : env_contract_states ?env ?caddr = Some _,
       deployed_state' : match env_contract_states ?env ?caddr with
                   | Some val => deserialize val
                   | None => None
                   end = Some ?cstate' |- _
      ] =>
        rewrite deployed_state in deployed_state'; inversion_subst deployed_state'
    | [deployed_state : match env_contract_states ?env ?caddr with
                   | Some val => deserialize val
                   | None => None
                   end = Some _,
       deployed_state' : match env_contract_states ?env ?caddr with
                   | Some val => deserialize val
                   | None => None
                   end = Some ?cstate' |- _
      ] =>
        rewrite deployed_state in deployed_state'; inversion_subst deployed_state'        
    end.  

  Definition build_act_ctx ctx msg : Action :=
    build_act ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
      (match msg with
          | None => act_transfer ctx.(ctx_contract_address) ctx.(ctx_amount)
          | Some m => act_call ctx.(ctx_contract_address) ctx.(ctx_amount) ((@serialize Msg _) m)
        end).

Section FunctionalProperties.

  Lemma ended_functional_correct (chain : Chain)
                           (ctx : ContractCallContext)
                           (prev_state next_state : State)
                           (msg : option Msg)
                           (acts : list ActionBody) :
    receive chain ctx prev_state msg = Ok (next_state, acts) ->
    (chain.(chain_height) <= prev_state.(auctionEndTime))%nat ->
    prev_state.(ended) = next_state.(ended).
  Proof.
    intros Hreceive no_end. 
    unfold receive in Hreceive.
    destruct msg; try discriminate.
    destruct m; unfold bid_step, withdraw_step, auction_end_step in Hreceive; cbn in *;
      try now contract_simpl.
    - (* withdraw *) 
      contract_simpl. 
      destruct (highestBidder prev_state);
      destruct (0 <? get_pendingReturns (ctx_from ctx) (pendingReturns prev_state));
      contract_simpl; cbn; try inversion Hreceive; auto.
    - (* AuctionEnd *)
      contract_simpl.  
      destruct (Nat.leb_spec (chain_height chain) (auctionEndTime prev_state)).
      discriminate. lia.
  Qed.

  Lemma auctionEndTime_functional_invariant (chain : Chain)
                           (ctx : ContractCallContext)
                           (prev_state next_state : State)
                           (msg : option Msg)
                           (acts : list ActionBody) :
    receive chain ctx prev_state msg = Ok (next_state, acts) ->
    prev_state.(auctionEndTime) = next_state.(auctionEndTime).
  Proof.
    intros Hreceive. 
    unfold receive in Hreceive.
    destruct msg; try discriminate.
    destruct m; unfold bid_step, withdraw_step, auction_end_step in Hreceive; cbn in *;
      try now contract_simpl.
    (* AuctionEnd *)
    contract_simpl.  
    destruct (0 <? get_pendingReturns (ctx_from ctx) (pendingReturns prev_state));
    destruct (highestBidder prev_state);  
    contract_simpl; cbn; auto.
  Qed.

End FunctionalProperties.

Section SafetyProperties.

  



  Lemma auctionEndTime_preserve (bstate : ChainState) caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate, 
      contract_state bstate caddr = Some cstate /\
      forall bstate',
        ChainTrace bstate bstate' ->
        exists cstate', 
          contract_state bstate' caddr = Some cstate' /\
          cstate'.(auctionEndTime) = cstate.(auctionEndTime). 
  Proof.
    intros reach deployed.
    specialize (deployed_contract_state_typed deployed) as (cstate & deployed_state); auto.
    exists cstate. split; auto. intros * trace.
    ChainTraceProperty.trace_induction.
    all: try (destruct IH as (cstate' & deployed_state' & end_eq)).
    - cbn in *. exists cstate. split; auto.
    - (* block *)
      exists cstate'. rewrite_environment_equiv. cbn. split; auto.  
    - (* valid *)
      action_trace_induction_intermidiate.
      + exists cstate'. split; auto. 
      + destruct IH as (cstate'' & deployed_state'' & end_eq'). 
        destruct_action_eval.
        * exists cstate''. rewrite_environment_equiv. cbn. split; auto. 
        * (* deploy *)
          exists cstate''. rewrite_environment_equiv. cbn in *. 
          destruct_address_eq; subst.
          --  
            enough (exists wc, env_contracts mid0 to_addr = Some wc).
            destruct H as (? & ?). congruence. 
            eapply @deployed_state_wc_typed_action_trace with (cstate := cstate''); auto.
            exists mid. destruct reach as [?].
            split.
            fold (ChainTrace bstate mid) in trace. 
            eapply chain_trace_trans; eauto.
            constructor; auto. 
          -- split; auto. 
        * (* call *)
          destruct (address_eqb_spec caddr to_addr); subst. 
          -- assert (deployed_mid : env_contracts mid to_addr = Some (contract : WeakContract)).
            eapply contract_preserve; eauto. 
            assert (deployed_mid0 : env_contracts mid0 to_addr = Some (contract : WeakContract)).
            eapply contract_preserve_action_trace; eauto. 
            split; auto. eapply reachable_trans; eauto. 
            inversion_deployed_contract.
            apply wc_receive_strong in receive_some.
            destruct receive_some as (prev_state_strong & msg_strong & new_state_strong
              & Hstate_eq & Hmsg & Hstate_new & receive_some). 
            exists new_state_strong.
            inversion_deployed_contract. 
            (* rewrite deployed_state0 in *. inversion_subst deployed_state''. *)
            destruct msg_strong; [destruct m|].
            ++ contract_simpl receive init.
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *. 
                inversion H3. rewrite deserialize_serialize. split; auto. 
                rewrite Hstate_eq in *. inversion_subst H0. auto. 
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *.
                discriminate.
            ++ (* withdraw *) 
              contract_simpl receive init.
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *. 
                inversion H2. rewrite deserialize_serialize. split; auto. 
                destruct (0 <? get_pendingReturns from_addr (pendingReturns prev_state_strong)); 
                destruct (highestBidder prev_state_strong); contract_simpl.
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *.
                discriminate.
            ++ (* AuctionEnd *) 
              contract_simpl receive init.
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *.
                inversion_subst H4. 
                rewrite deserialize_serialize. split; auto. rewrite <- end_eq'. 
                rewrite Hstate_eq in *. inversion H0. auto. 
              ** rewrite_environment_equiv. cbn in *. rewrite address_eq_refl in *.
                discriminate. 
            ++ (* None *) 
              contract_simpl receive init.            
          -- exists cstate''. rewrite_environment_equiv. cbn. rewrite address_eq_ne; auto. 
    - (* invalid *)
      exists cstate'. rewrite_environment_equiv. cbn. split; auto.
  Qed. 

  
  Lemma ended_correct {bstate caddr} :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists (cstate : State),
      contract_state bstate caddr = Some cstate /\
      ((bstate.(chain_height) <= cstate.(auctionEndTime))%nat ->
      cstate.(ended) = false).
  Proof. 
    contract_induction; intros; auto.
    - (* add_block *)
      apply IH. 
      instantiate (AddBlockFacts := fun old_chain_height _ _ new_chain_height _ _ => 
        (old_chain_height < new_chain_height)%nat). 
      now destruct facts.
    - (* deploy *)
      now contract_simpl.
    - (* call *)
       
      cbn in *.
      erewrite ended_functional_correct with (next_state := new_state) in IH. 
      apply IH.
      erewrite (auctionEndTime_functional_invariant); eauto. 
      apply receive_some. 
      erewrite (auctionEndTime_functional_invariant); eauto; lia. 
    - (* call *) 
      cbn in *.
      erewrite ended_functional_correct with (next_state := new_state) in IH. 
      apply IH.
      erewrite (auctionEndTime_functional_invariant); eauto. 
      apply receive_some. 
      erewrite (auctionEndTime_functional_invariant); eauto; lia. 
    - (* facts *)
      solve_facts.
      destruct valid_header. lia.
  Qed.

End SafetyProperties.

Section LivenessProperties.

  (* a crucial correctness property of this application is a liveness property: 
    If an actor makes a bid, that actor will eventually either 
      win the auction and be assigned ownership of the desired item, 
      or 
      they will get their money back *)
  Definition can_close caddr seller_addr (st : ChainState) : Prop := 
    forall ctx, 
      List.hd_error st.(chain_state_queue) = Some (build_act_ctx ctx (Some AuctionEnd)) -> 
      valid_token_ctx st ctx ->
      (ctx.(ctx_amount) <= 0) -> (* not payable *)
      seller_addr = ctx.(ctx_from) -> 
      caddr = ctx.(ctx_contract_address) ->
      pre contract (Some AuctionEnd) st ctx. 

  




  Lemma eventually_claim : 
    forall (caddr : Address) (bstate_from : ChainState),
      reachable bstate_from ->
      env_contracts bstate_from caddr = Some (contract : WeakContract) ->
      (exists cstate, 
        contract_state bstate_from caddr = Some cstate /\
        (bstate_from.(chain_height) <= cstate.(auctionEndTime))%nat) -> 
      forall (str : ChainStream),
        path str ->
        Str_nth 0 str = bstate_from ->
        exists n, 
          (* finally happen *)
          (fun caddr (st : ChainState) =>
           exists cstate, 
             contract_state st caddr = Some cstate /\
             can_close caddr cstate.(beneficiary) st) 
          caddr 
          (Str_nth n str).
  Proof.
    pose (f := fun caddr (st : ChainState) =>
      match (contract_state st caddr) with
      | Some cstate => Some (S cstate.(auctionEndTime) - st.(chain_height))%nat
      | None => None
      end).
    intros * reach deployed Hfrom.

    eapply (Liveness_rank_opt_first_bottom (A := nat)) 
      with (f := f) (bot := 0%nat); eauto.
    apply lt_wf.
    apply Nat.eq_dec.
    - (* start *)
      destruct Hfrom as (cstate & deployed_state & no_end).
      exists (S (auctionEndTime cstate) - chain_height bstate_from)%nat.
      unfold f. rewrite deployed_state. split; auto. 
      intros contra. lia. 
    - (* eventually decrease *)
      intros * reach_th Hrank1 no_bot.
      unfold f in Hrank1. 
      assert (reach' : reachable bstate) by (eapply reachable_through_reachable; eauto).
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace) as (deployed' & cstate & deployed_state).
      rewrite deployed_state in *. inversion_subst Hrank1.
      intros * Hstart Hpath.
      specialize (chain_height_increase bstate (S (chain_height bstate))
        ltac:(auto) ltac:(lia)) as (n & increase_height); eauto.
      exists n, (S (auctionEndTime cstate) - S (chain_height bstate))%nat.
      split; only 2: lia.
        (** (Str_nth n str) ranked Some **)
      unfold f. 
      specialize (stream_n_trace bstate str n) as [trace']; auto.
      specialize (contract_preserve reach' deployed' trace')
          as (deployed'' & cstate' & deployed_state').
      rewrite deployed_state'. rewrite increase_height.
      destruct reach as [reach].
      assert (inhabited (ChainTrace empty_state bstate)) as [trace_bstate].
      eapply chain_trace_trans; eauto.
      specialize (auctionEndTime_preserve bstate caddr)
        as (cstate'0 & deployed_state0 & Hpreserve); auto. 
      specialize (Hpreserve (Str_nth n str) trace') as
        (cstate''0 & deployed_state'0 & end_eq').
      repeat inversion_deployed_contract. 
      now rewrite end_eq'. 
    - (* finally *)
      unfold can_close, f.
      intros * reach_th step prev_not_bot next_bot.
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace)
        as (deployed_prev & cstate_prev & deployed_state_prev). 
      specialize (contract_preserve reach deployed (snoc trace step))
        as (deployed_next & cstate_next & deployed_state_next).  
      exists cstate_next. split; auto. 
      intros * queue valid no_pay seller_addr caddr_eq. 
      unfold pre. 
      split; auto. 
      apply reachable_action_trace_reahcable_in_action_trace_iff.
      exists next. apply reachable_in_action_trace_refl.
      eapply reachable_trans; eauto. apply (snoc trace step). 
      split; auto. 
      split; auto. 
      rewrite <- caddr_eq in *.
      split; auto. 
      exists cstate_next,
        (setter_from_getter_State_ended (fun _ : bool => true) cstate_next),
         [act_transfer (beneficiary cstate_next) (highestBid cstate_next)]. 
      split; auto. 
      evaluate_receive. 
      + (* no end *) (* invariant *)
        rewrite deployed_state_prev in prev_not_bot. 
        assert (not_bot : (S (auctionEndTime cstate_prev) - chain_height prev)%nat <> 0%nat) by congruence.
        assert (reach_prev : reachable prev) by (eapply reachable_trans; eauto).
        specialize (@ended_correct prev caddr)
          as (cstate_prev' & deployed_state_prev' & no_end); auto.
        inversion_deployed_contract.
        specialize (auctionEndTime_preserve prev (ctx_contract_address ctx))
          as (cstate'0 & deployed_state0 & Hpreserve); auto. 
        specialize (Hpreserve next) as (cstate_next' & deployed_state_next' & end_eq).
        apply (snoc clnil step).
        repeat inversion_deployed_contract. 
        rewrite end_eq in *.
          
        assert (add_height : (chain_height prev < chain_height next)%nat). 
        { 
          assert ((S (auctionEndTime cstate'0) > chain_height prev)%nat).
          lia. 
          destruct (Nat.leb_spec (chain_height next) (auctionEndTime cstate'0)); try discriminate. 
          lia.
        }
        destruct_chain_step. 
        * (* add block *)
          rewrite_environment_equiv; cbn in *. 
          repeat inversion_deployed_contract.
          apply no_end. lia.
        * (* valid *)
          now specialize (action_trace_chain_height_invariant action_trace).
        * (* invalid *)
          rewrite_environment_equiv. lia.
      + (* exceed auctionEndTime *)
        rewrite deployed_state_next in next_bot. inversion next_bot. 
        apply Nat.le_0_r in H0. apply Nat.leb_nle. lia.
      + (* not payable *)
        lia.
  Qed.

  
  Lemma eventually_claim' : 
    forall (caddr : Address) (bstate_from : ChainState),
      reachable bstate_from ->
      env_contracts bstate_from caddr = Some (contract : WeakContract) ->
      (exists cstate, 
        contract_state bstate_from caddr = Some cstate /\
        (bstate_from.(chain_height) <= cstate.(auctionEndTime))%nat) -> 
      liveness bstate_from
        (fun (st : ChainState) =>
          exists cstate, 
            contract_state st caddr = Some cstate /\
            can_close caddr cstate.(beneficiary) st).
  Proof.
    pose (f := fun caddr (st : ChainState) =>
      match (contract_state st caddr) with
      | Some cstate => Some (S cstate.(auctionEndTime) - st.(chain_height))%nat
      | None => None
      end).
    pose (0%nat) as bot.
    intros * reach deployed Hpre.
    proof_liveness f bot.
    apply lt_wf.
    apply Nat.eq_dec.
    - (* start *)
      destruct Hpre as (cstate & deployed_state & no_end).
      exists (S (auctionEndTime cstate) - chain_height bstate_from)%nat.
      unfold f. rewrite deployed_state. split; auto. 
      intros contra.
      lia. 
    - (* eventually decrease *)
      intros * reach_th Hrank1 no_bot.
      unfold f in Hrank1. 
      assert (reach' : reachable bstate) by (eapply reachable_through_reachable; eauto).
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace) as (deployed' & cstate & deployed_state).
      rewrite deployed_state in *. inversion_subst Hrank1.
      intros * Hstart' Hpath'.
      
      specialize (chain_height_increase bstate (S (chain_height bstate))
        ltac:(auto) ltac:(lia)) as (n & increase_height); eauto.
      
      exists n, (S (auctionEndTime cstate) - S (chain_height bstate))%nat.
      split; only 2: lia.
        (** (Str_nth n str) ranked Some **)
      unfold f. 
      specialize (stream_n_trace bstate str0 n) as [trace']; auto.
      specialize (contract_preserve reach' deployed' trace')
          as (deployed'' & cstate' & deployed_state').
      rewrite deployed_state'. rewrite increase_height.
      destruct reach as [reach].
      assert (inhabited (ChainTrace empty_state bstate)) as [trace_bstate].
      eapply chain_trace_trans; eauto.
      
      specialize (auctionEndTime_preserve bstate caddr)
        as (cstate'0 & deployed_state0 & Hpreserve); auto. 
      specialize (Hpreserve (Str_nth n str0) trace') as
        (cstate''0 & deployed_state'0 & end_eq').
      repeat inversion_deployed_contract. 
      now rewrite end_eq'. 
    - (* finally *) 
      unfold can_close, f.
      intros * reach_th step prev_not_bot next_bot.
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace)
        as (deployed_prev & cstate_prev & deployed_state_prev). 
      specialize (contract_preserve reach deployed (snoc trace step))
        as (deployed_next & cstate_next & deployed_state_next).  
      exists cstate_next. split; auto. 
      intros * queue valid no_pay seller_addr caddr_eq. 
      unfold pre. 
      split; auto. 
      apply reachable_action_trace_reahcable_in_action_trace_iff.
      exists next. apply reachable_in_action_trace_refl.
      eapply reachable_trans; eauto. apply (snoc trace step). 
      split; auto. 
      split; auto. 
      rewrite <- caddr_eq in *.
      split; auto. 
      exists cstate_next,
        (setter_from_getter_State_ended (fun _ : bool => true) cstate_next),
         [act_transfer (beneficiary cstate_next) (highestBid cstate_next)]. 
      split; auto. 
      evaluate_receive. 
      + (* no end *) (* invariant *)
        rewrite deployed_state_prev in prev_not_bot. 
        assert (not_bot : (S (auctionEndTime cstate_prev) - chain_height prev)%nat <> 0%nat) by congruence.
        assert (reach_prev : reachable prev) by (eapply reachable_trans; eauto).
        specialize (@ended_correct prev caddr)
          as (cstate_prev' & deployed_state_prev' & no_end); auto.
        inversion_deployed_contract.
        specialize (auctionEndTime_preserve prev (ctx_contract_address ctx))
          as (cstate'0 & deployed_state0 & Hpreserve); auto. 
        specialize (Hpreserve next) as (cstate_next' & deployed_state_next' & end_eq).
        apply (snoc clnil step).
        repeat inversion_deployed_contract. 
        rewrite end_eq in *.
          
        assert (add_height : (chain_height prev < chain_height next)%nat). 
        { 
          assert ((S (auctionEndTime cstate'0) > chain_height prev)%nat).
          lia. 
          destruct (Nat.leb_spec (chain_height next) (auctionEndTime cstate'0)); try discriminate. 
          lia.
        }
        destruct_chain_step. 
        * (* add block *)
          rewrite_environment_equiv; cbn in *. 
          repeat inversion_deployed_contract.
          apply no_end. lia.
        * (* valid *)
          now specialize (action_trace_chain_height_invariant action_trace).
        * (* invalid *)
          rewrite_environment_equiv. lia.
      + (* exceed auctionEndTime *)
        rewrite deployed_state_next in next_bot. inversion next_bot. 
        apply Nat.le_0_r in H0. apply Nat.leb_nle. lia.
      + (* not payable *)
        lia.
  Qed.

End LivenessProperties.

Section Wip. 
  


  Definition close caddr : ChainState -> ChainState -> Prop :=
    fun _ st => 
      exists (cstate : State), 
        contract_state st caddr = Some cstate /\
        cstate.(ended) = true.
  
  Definition post (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (prev next : ChainState) (ctx : ContractCallContext) 
                 acts
                 : Prop :=
    reachable_action_trace prev /\
    inhabited (ActionChainStep prev next) /\
    prev.(chain_state_queue) = (build_act ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) 
      (match msg with
          | None => act_transfer ctx.(ctx_contract_address) ctx.(ctx_amount)
          | Some m => act_call ctx.(ctx_contract_address) ctx.(ctx_amount) ((@serialize Msg _) m)
        end)) 
      :: acts /\
    (* address_is_contract ctx.(ctx_contract_address) = true. *)
    env_contracts prev ctx.(ctx_contract_address) = Some (contract : WeakContract).

  Definition enabled_pred_forall (contract : Contract Setup Msg State Error)
                 (c : ChainState -> ChainState -> Prop)
                 (st : ChainState) :=
    forall prev ctx (acts : list Action),
      ActionChainStep prev st ->
      valid_token_ctx st ctx ->
      exists (msg : option Msg),
        enabled contract msg prev ctx /\
        post contract msg prev st ctx acts /\ 
        c prev st.

  

  Lemma enabled_close (bstate : ChainState) caddr :
    reachable_action_trace bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists (cstate : State),
      contract_state bstate caddr = Some cstate /\
      (bstate.(chain_height) > cstate.(auctionEndTime))%nat ->
      (enabled_pred_forall SimpleAuction.contract (close caddr)) bstate.
  Proof.
    intros (origin & reach & [action_trace]) deployed.
    destruct reach as [trace].
    remember empty_state; induction trace; subst.
    {
      destruct (action_trace_step action_trace) as [|(mid & [step] & [action_trace'])]; subst; cbn in *; try congruence.
      destruct_action_chain_step. cbn in *. congruence.
    }

    
    assert (
      preserve_through_action_trace : forall st1 st2
            (trace : ChainTrace empty_state st1)
            (action_trace : ActionChainTrace st1 st2),
        env_contracts st2 caddr = Some (contract : WeakContract) ->
        exists (cstate : State), 
          contract_state st2 caddr = Some cstate /\
          (chain_height st2 > auctionEndTime cstate)%nat ->
          enabled_pred_forall contract (close caddr) st2
    ).
    {
      clear trace l action_trace deployed IHtrace.
      intros st1 st2 trace' action_trace' contract_deployed'.
      remember st1; induction action_trace' as [|? at_mid at_to action_trace' IHat at_step]; 
        subst; cbn in *; auto.
      {
        (* clnil *)
      
    

  Abort.

  Definition enabled_forall (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) : Prop :=
    forall ctx,
      valid_token_ctx st ctx ->
      env_contracts st ctx.(ctx_contract_address) = Some (contract : WeakContract) ->
      pre contract msg st ctx (List.tl st.(chain_state_queue)).

  Definition pre (contract : Contract Setup Msg State Error) (msg : option Msg)
                 (st : ChainState) (ctx : ContractCallContext) acts
                  : Prop :=
    let limit := ctx.(ctx_limit) in
    let origin_addr := ctx.(ctx_origin) in
    let from_addr := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    let amount := ctx.(ctx_amount) in
    reachable_action_trace st ->
    st.(chain_state_queue) = (build_act limit origin_addr from_addr
      (match msg with
          | None => act_transfer caddr amount
          | Some m => act_call caddr amount ((@serialize Msg _) m)
        end)) 
      :: acts ->
    (0 < limit)%nat /\
    (0 <= amount)%Z /\
    (env_account_balances st from_addr >= amount)%Z /\
    env_contracts st caddr = Some (contract : WeakContract) /\
    exists (cstate : State) (new_cstate : State) (new_acts : list ActionBody),
      contract_state st caddr = Some cstate /\ 
      receive  
          (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) st) 
          (* (ctx<|ctx_contract_balance := 
              if (address_eqb from_addr caddr)
                  then (env_account_balances st caddr)
                  else ((env_account_balances st caddr) + amount)%Z|>) *)
          {| ctx_origin := origin_addr;
             ctx_from := from_addr;
             ctx_contract_address := caddr;
             ctx_contract_balance := if (address_eqb from_addr caddr)
                  then (env_account_balances st caddr)
                  else ((env_account_balances st caddr) + amount)%Z;
             ctx_amount := amount;
             ctx_limit := limit
          |}
          cstate msg
        = Ok (new_cstate, new_acts).

  



  Definition claim caddr : ChainState -> Prop :=
    fun st => 
      forall ctx acts,
      valid_token_ctx st ctx ->
      exists (cstate : State), 
        contract_state st caddr = Some cstate /\
        ctx.(ctx_from) = cstate.(beneficiary) ->
        pre contract (Some AuctionEnd) st ctx acts.

  Lemma seller_classical_liveness bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    pAF (claim caddr) bstate.
  Proof.
    intros reach deployed.
    specialize (deployed_contract_state_typed deployed reach) as (cstate & deployed_state).
    pose (f := fun (_ : Address) (st : ChainState) => 
      (cstate.(auctionEndTime) - st.(chain_height))%nat).
    pose (P_pre := fun (caddr : Address) (st : ChainState) => 
      env_contracts st caddr = Some (contract : WeakContract)).
    unfold pAF.
    eapply (Liveness_rank_nat) with (f := f) (P_pre := P_pre); eauto.
    - (* decrease *)
      admit.
    - (* eventually *) 
      unfold claim.
      intros * bottom * valid_ctx.
      assert (reach_th : reachable_through bstate st). admit.
      
      unfold pre. 
      






    

  Lemma enabled_close' (bstate : ChainState) caddr :
    reachable_action_trace bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists (cstate : State),
      (bstate.(chain_height) > cstate.(auctionEndTime))%nat ->
      pAF (enabled_pred_forall SimpleAuction.contract (close caddr)) bstate.

  Lemma auctionEndTime_invariant {bstate caddr} 
      (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate dep,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      cstate.(auctionEndTime) = dep.(deployment_setup).(biddingTime).
  Proof.
    contract_induction; intros; auto.
    - (* dep *)
      cbn in *. contract_simpl receive init. cbn.
  Admitted.

  


  Lemma wip_eventually_claim : 
    forall (caddr : Address) (bstate_from : ChainState),
      reachable bstate_from ->
      env_contracts bstate_from caddr = Some (contract : WeakContract) ->
      (exists cstate, 
        contract_state bstate_from caddr = Some cstate /\
        (bstate_from.(chain_height) < cstate.(auctionEndTime))%nat) ->
      forall (str : ChainStream),
        path str ->
        Str_nth 0 str = bstate_from ->
        exists n, 
          (fun caddr (st : ChainState) =>
           exists cstate, 
             contract_state st caddr = Some cstate /\
             can_close caddr cstate.(beneficiary) st) 
          caddr 
          (Str_nth n str).
  Proof.
    pose (f := fun caddr (st : ChainState) =>
      match (contract_state st caddr) with
      | Some cstate => Some (cstate.(auctionEndTime) - st.(chain_height))%nat
      | None => None
      end).
    intros * reach deployed no_end.
    eapply (Liveness_rank_wf_opt_strong (A := nat)) 
      with (f := f) (P_pre := fun _ _ => True) (bot := 0%nat); eauto.
    apply lt_wf.
    apply Nat.eq_dec.
    intros _. 
    - (* start *)
      specialize (deployed_contract_state_typed deployed)
        as (cstate & deployed_state); auto.
      exists (auctionEndTime cstate - chain_height bstate_from)%nat.
      unfold f. rewrite deployed_state. auto. 
    - (* eventually decrease *)
      intros * reach_th Hrank1 no_bot.
      unfold f in Hrank1. 
      assert (reach' : reachable bstate) by (eapply reachable_through_reachable; eauto).
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace) as (deployed' & cstate & deployed_state).
      rewrite deployed_state in *. inversion_subst Hrank1.
      intros * Hstart Hpath.
      specialize (chain_height_increase bstate (S (chain_height bstate))
        ltac:(auto) ltac:(lia)) as (n & increase_height); eauto.
      exists n, (auctionEndTime cstate - S (chain_height bstate))%nat.
      split.
      + unfold f. 
        specialize (stream_n_trace bstate str n) as [trace']; auto.
        specialize (contract_preserve reach' deployed' trace')
           as (deployed'' & cstate' & deployed_state').
        rewrite deployed_state'. rewrite increase_height.
        destruct reach as [reach].
        assert (inhabited (ChainTrace empty_state bstate)) as [trace_bstate].
        eapply chain_trace_trans; eauto.
        specialize (auctionEndTime_invariant trace_bstate deployed')
          as (cstate'0 & dep & Hdep & deployed_state0 & end_eq). 
        rewrite deployed_state0 in *. inversion_subst deployed_state. 
        rewrite end_eq.
        specialize (auctionEndTime_invariant (clist_app trace_bstate trace') deployed'')
          as (cstate''0 & dep' & Hdep' & deployed_state'0 & end_eq').
        rewrite deployed_state'0 in *. inversion_subst deployed_state'.
        rewrite end_eq'. 
        specialize (deployment_info_invariant trace_bstate deployed')
          as (dep0 & Hdep0 & dep_info_eq).
        rewrite Hdep in *. inversion Hdep0. subst dep0. clear Hdep0.
        rewrite dep_info_eq in Hdep'. inversion_subst Hdep'. auto.
      + lia.
    - (* finally *)
      unfold can_close, f.
      intros * reach_th Hbot.
      (* specialize (deployed_contract_state_typed deployed)
        as (cstate & deployed_state); auto. *)
      destruct reach_th as (_ & [trace]). 
      specialize (contract_preserve reach deployed trace)
        as (deployed_st & cstate & deployed_state_st).  
      exists cstate. split; auto. 
      intros * queue valid no_pay seller_addr caddr_eq. 
      unfold pre. 
      split; auto. 
      apply reachable_action_trace_reahcable_in_action_trace_iff.
      exists st. apply reachable_in_action_trace_refl. destruct reach as [reach]. 
      eapply chain_trace_trans; eauto.
      split; auto. 
      split; auto. 
      split; auto. 
      rewrite <- caddr_eq. auto. 
      exists cstate,
        (setter_from_getter_State_ended (fun _ : bool => true) cstate),
         [act_transfer (beneficiary cstate) (highestBid cstate)]. 
      split; auto. 
      rewrite <- caddr_eq. auto.
      evaluate_receive.
  Abort. 

End Wip.

End Theories.
