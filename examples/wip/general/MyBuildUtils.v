From Coq Require Import Logic.Decidable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Examples.Wip.General Require Import Blockchain_modify_2.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify_2.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import ContractCommon_modify_2.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.
From Coq Require Import Lia.
From Coq Require Import Streams.
From ConCert.Examples.Wip.TemporalLogic Require Import Agreement.
From ConCert.Examples.Wip.Ppl2026 Require Import Liveness.
From ConCert.Execution Require Import Serializable.

From Coq Require Import Arith.Wf_nat.
From Coq Require Import Wellfounded.
From Coq Require Import Wellfounded.Lexicographic_Product.
From Coq Require Import Relations.Relation_Operators.
From ConCert.Examples.Wip.General Require Import ChainStreamProperty.


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

Section MyBuildUtils.
Context {BaseTypes : ChainBase}.

  Ltac action_trace_induction_intermidiate :=
    match goal with
    | H : ActionChainTrace ?mid ?to |- _ =>
        
        pattern to;
        match goal with
        | |- ?P to =>
            let A := fresh "A" in
            enough (forall st, ActionChainTrace mid st -> P st) as A;
            [ 
              eapply A; eauto
            | 
            ]
        end
    end.

  Lemma wc_receive_to_receive_None : forall {Setup Msg State Error : Type}
                                    `{Serializable Setup}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                    `{Serializable Error}
                                    (contract : Contract Setup Msg State Error)
                                    chain cctx cstate new_cstate new_acts s,
  deserialize s = Some cstate ->
  contract.(receive) chain cctx cstate None = Ok (new_cstate, new_acts) <->
    wc_receive contract chain cctx s None = Ok ((@serialize State _) new_cstate, new_acts).
  Proof.
    intros * deser_some. split.
    - cbn. intro receive_some. rewrite deser_some; cbn. 
      rewrite receive_some. cbn. auto.
    - intros wc_receive_some.
      apply wc_receive_strong in wc_receive_some as
        (prev_state' & msg' & new_state' & prev_state_eq & msg_eq & new_state_eq & receive_some).
      apply serialize_injective in new_state_eq. subst.
      rewrite deser_some in *. inversion_subst prev_state_eq.
      destruct msg' eqn:Hmsg; cbn in msg_eq; congruence.
  Qed. 

  Lemma contract_preserve
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {bstate bstate' : ChainState}
            {caddr} :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    ChainTrace bstate bstate' ->
    env_contracts bstate' caddr = Some (contract : WeakContract)  /\
    exists (cstate : State), 
      contract_state bstate' caddr = Some cstate.
  Proof.
    intros reach deployed trace.
    remember bstate; induction trace; subst.
    - split; auto.
      eapply @deployed_contract_state_typed with (contract := contract); eauto.
    - 
      (* specialize (deployed_contract_state_typed deployed) 
        as (cstate & deployed_state); auto. *)
      specialize_hypotheses.
      specialize IHtrace as (deployed_mid & cstate & deployed_state).
      clear deployed.
      destruct_chain_step; 
        try (split; only 2: (exists cstate); rewrite_environment_equiv; auto).
      action_trace_induction_intermidiate.
      intros * action_trace'.
      remember mid; induction action_trace'; subst.
      split; only 2: exists cstate; auto.
      specialize_hypotheses.
      specialize IHaction_trace' 
        as (deployed_mid' & cstate' & deployed_state'). 
      destruct_action_chain_step.
      destruct_action_eval.
      + (* transfer *)
        split; only 2: exists cstate'; rewrite_environment_equiv; auto.
      +
        destruct (address_eqb_spec caddr to_addr); subst; try congruence.
        split; only 2: exists cstate'; rewrite_environment_equiv; cbn;
          rewrite address_eq_ne; auto.
      +
        split. 
        rewrite_environment_equiv; auto.
        destruct (address_eqb_spec caddr to_addr); subst.
        * 
          rewrite deployed in *. inversion_subst deployed_mid'.
          eapply wc_receive_strong in receive_some
            as (? & ? & cstate'' & ? & ? & ? & ?).
          exists cstate''. (* kari *)
          rewrite_environment_equiv; cbn. 
          rewrite address_eq_refl.
          subst. rewrite deserialize_serialize; auto.
        *  
          exists cstate'.
          rewrite_environment_equiv. cbn.
          rewrite address_eq_ne; auto.
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

  Local Ltac rewrite_queue :=
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *
      end.

  Lemma stream_path_nth_tl {n} {str} :
    path str -> path (Str_nth_tl n str).
  Proof.
    unfold path.
    intros Hpath k.
    rewrite !Str_nth_plus.
    replace ((k + 1) + n) with ((k + n) + 1) by lia.
    exact (Hpath (k + n)).
  Qed.

  Lemma empty_queue_finally bstate :
    reachable bstate ->
    forall str, 
      path str -> 
      Str_nth 0 str = bstate ->
      let n := length bstate.(chain_state_queue) in 
      (Str_nth n str).(chain_state_queue) = [] /\
      (Str_nth n str).(chain_height) = bstate.(chain_height).
  Proof.
    remember (length (chain_state_queue bstate)) as n.
    generalize dependent bstate.
    induction n.
    {
      intros * Hlen reach * Hpath Hstart. cbn.
      destruct (chain_state_queue bstate) eqn:queue; cbn in *; try lia.
      subst. split; auto.
    }
    intros * Hlen reach * Hpath Hstart.
    pose Hpath as Hpath'.
    unfold path in Hpath'. specialize (Hpath' 0) as [step].
    cbn in *.
    destruct_chain_step; subst.
    - rewrite_queue. cbn in *. lia.
    - rewrite_queue. inversion Hlen.
      specialize (IHn (Str_nth 1 str)) as (queue_nil & height_eq); auto.
      eapply stream_reahcable; eauto.
      apply stream_path_nth_tl; auto.
      rewrite Str_nth_plus, Nat.add_1_r in *. subst n.
      split; auto.
      rewrite (action_trace_chain_height_invariant action_trace).
      auto.
    - rewrite_queue. inversion Hlen.
      specialize (IHn (Str_nth 1 str)) as (queue_nil & height_eq); auto.
      eapply stream_reahcable; eauto.
      apply stream_path_nth_tl; auto.
      rewrite Str_nth_plus, Nat.add_1_r in *. subst n.
      split; auto.
      rewrite_environment_equiv. auto. 
  Qed.

  
  Lemma chain_height_increase bstate : forall n,
    reachable bstate ->
    (bstate.(chain_height) <= n)%nat ->
    pAF (fun st => st.(chain_height) = n) bstate.
  Proof.
    intro n. 
    remember (n - bstate.(chain_height))%nat as diff.
    generalize dependent bstate. induction diff.
    {
      intros.
      unfold pAF, p_finally. intros. exists 0. subst. lia.
    }
    intros * Hdiff reach Hheight.
    unfold pAF in *. intros * Hpath Hstart.
    specialize (empty_queue_finally bstate) as [queue_empty height_eq]; eauto.
    pose Hpath as Hpath'. unfold path in Hpath'.
    destruct (Hpath' (length bstate.(chain_state_queue))) as [step]. rewrite Nat.add_1_r in *.
    destruct_chain_step; rewrite_queue; try congruence.
    destruct valid_header.
    unfold p_finally in *.
    specialize (IHdiff (Str_nth (S (length (chain_state_queue bstate))) str)
      ) as (n' & height_eq'); auto.
    rewrite_environment_equiv. cbn. lia. 
    eapply stream_reahcable; eauto.
    rewrite_environment_equiv. cbn. lia. 
    apply stream_path_nth_tl; auto.
    exists (n' + S (length (chain_state_queue bstate))).
    rewrite Str_nth_plus in *. auto.
  Qed.

  
  Ltac trace_induction :=
  match goal with
  | trace : ChainTrace empty_state ?bstate |- _ =>
    cbn;
    remember empty_state;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = empty_state |- _ => subst x
    end;
    [try discriminate |
    (* destruct_chain_step; try destruct_action_eval;
    match goal with
    | env_eq : EnvironmentEquiv _ _ |- _ =>
        try rewrite env_eq in *; try setoid_rewrite env_eq
    end; *)
    repeat (specialize (IH ltac:(auto)))
    ]; auto
  end.

  Lemma deployed_deployment_info_typed
          {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
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
    (* Show that eq is a contradiction. *)
    remember empty_state; induction trace; subst; cbn in *; try congruence.
    destruct_chain_step; try now rewrite_environment_equiv.
    enough (at_deployed_deployment_info_typed :
           forall {st : ChainState} (action_trace : ActionChainTrace mid st),
        env_contracts st caddr = Some (contract : WeakContract) ->
        exists dep_info,
          deployment_info_in_action_trace Setup trace action_trace caddr = Some dep_info).
    {
      (* enough *)
      specialize (at_deployed_deployment_info_typed to action_trace ltac:(auto))
        as (dep_info & Hdep).
      (* unfold act_trace_deployment_info in eq.  *)
      unfold deployment_info_in_action_trace in Hdep.
      destruct (act_trace_deployment_info Setup action_trace caddr); congruence.
    }
    intros * deployed_st.
    remember mid; induction action_trace0; subst.
    {
      (* empty *)
      destruct (act_trace_deployment_info Setup action_trace caddr); try congruence.
      specialize_hypotheses.
      specialize IHtrace as (dep_info & ?). discriminate. 
    }
    specialize_hypotheses. 
    destruct_action_chain_step. destruct_action_eval; subst.
    - (* transfer *)
      rewrite_environment_equiv. cbn in *.
      specialize (IHaction_trace0) as (dep_info & dep_some); auto.
      exists dep_info.
      unfold deployment_info_in_action_trace in *. cbn. 
      destruct (act_trace_deployment_info Setup action_trace0 caddr); congruence.
    - (* deploy *)
      rewrite_environment_equiv. cbn in *.
      destruct (address_eqb_spec caddr to_addr).
      + (* deploy now *)
        destruct ((@deserialize Setup _) setup) eqn: Hsetup.
        * (* Some *)
          exists (build_deployment_info origin from_addr amount s).
          unfold deployment_info_in_action_trace. cbn. subst to_addr.
          rewrite address_eq_refl, Hsetup. auto.
        * (* None *)
          cbn in init_some. inversion_subst deployed_st. 
          specialize (wc_init_strong init_some) 
            as (setup_strong & result_strong & contra & _).
          congruence. 
      + (* already deployed *)
        specialize (IHaction_trace0) as (dep_info & dep_some); auto.
        exists dep_info.
        unfold deployment_info_in_action_trace in *. cbn. 
        rewrite (address_eq_ne); auto.
    - (* call *)
      rewrite_environment_equiv. cbn in *.
      specialize (IHaction_trace0) as (dep_info & dep_some); auto.
      exists dep_info.
      unfold deployment_info_in_action_trace in *. cbn. 
      destruct (act_trace_deployment_info Setup action_trace0 caddr); congruence.
  Qed.

  Lemma contract_preserve_action_trace
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {bstate bstate' : ChainState}
            {caddr} :
    reachable_in_action_trace bstate bstate' ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    env_contracts bstate' caddr = Some (contract : WeakContract)  /\
    exists (cstate : State), 
      contract_state bstate' caddr = Some cstate.
  Proof.
    intros (reach & [trace]) deployed.
    remember bstate; induction trace; subst.
    - split; auto.
      eapply @deployed_contract_state_typed with (contract := contract); eauto.
    - 
      specialize_hypotheses.
      specialize IHtrace as (deployed_mid & cstate & deployed_state).
      clear deployed.
      destruct_action_chain_step.
      destruct_action_eval.
      + (* transfer *)
        split; only 2: exists cstate; rewrite_environment_equiv; auto.
      +
        destruct (address_eqb_spec caddr to_addr); subst; try congruence.
        split; only 2: exists cstate; rewrite_environment_equiv; cbn;
          rewrite address_eq_ne; auto.
      +
        split. 
        rewrite_environment_equiv; auto.
        destruct (address_eqb_spec caddr to_addr); subst.
        * 
          rewrite deployed in *. inversion_subst deployed_mid.
          eapply wc_receive_strong in receive_some
            as (? & ? & cstate' & ? & ? & ? & ?).
          exists cstate'. (* kari *)
          rewrite_environment_equiv; cbn. 
          rewrite address_eq_refl.
          subst. rewrite deserialize_serialize; auto.
        *  
          exists cstate.
          rewrite_environment_equiv. cbn.
          rewrite address_eq_ne; auto.
  Qed.

  Lemma weak_contract_preserve_action_trace
            {bstate bstate' : ChainState}
            {caddr} {wc} :
    reachable_in_action_trace bstate bstate' ->
    env_contracts bstate caddr = Some wc ->
    env_contracts bstate' caddr = Some wc.
  Proof.
    intros (reach & [trace]) deployed.
    action_trace_induction.
    destruct_action_eval.
    + (* transfer *)
      rewrite_environment_equiv; auto.
    +
      destruct (address_eqb_spec caddr to_addr); subst; try congruence.
      rewrite_environment_equiv; cbn; rewrite address_eq_ne; auto.
    +
      rewrite_environment_equiv; auto.
  Qed.

  Lemma deployment_info_invariant 
          {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
          {contract : Contract Setup Msg State Error} 
          {bstate : ChainState} {caddr} 
          (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists (dep_info : DeploymentInfo Setup),
      deployment_info Setup trace caddr = Some dep_info /\
      forall bstate' (trace' : ChainTrace bstate bstate'),
        deployment_info Setup (clist_app trace trace') caddr = Some dep_info.
  Proof.
    intros deployed.
    specialize (deployed_deployment_info_typed trace deployed) 
      as (dep_info & Hdep).
    exists dep_info. split; auto. 
    intros *. 
    remember bstate; induction trace'; subst; cbn; auto. 
    specialize_hypotheses.
    destruct_chain_step; auto.
    enough (at_deployment_info_invariant :
          forall {st : ChainState} (action_trace : ActionChainTrace mid st),
      act_trace_deployment_info Setup action_trace caddr = None).
    {
      (* enough *)
      rewrite at_deployment_info_invariant; auto.
    }
    intros.
    remember mid; induction action_trace0; subst; cbn in *; auto. 
    specialize_hypotheses.
    destruct_action_chain_step. destruct_action_eval; subst; cbn in *; auto.
    destruct (address_eqb_spec to_addr caddr); subst; auto.
    assert (deployed_mid : env_contracts mid caddr = Some (contract : WeakContract)).
    {
      eapply contract_preserve; eauto. constructor; auto.
    }
    assert (reach_at : reachable_in_action_trace mid mid0).
    {
      split. eapply chain_trace_trans; eauto.
      constructor; auto.
    }
    specialize (contract_preserve_action_trace reach_at deployed_mid) as 
      (? & _).
    congruence.
  Qed.  

  Lemma deployed_state_wc_typed
            {State : Type} `{Serializable State}
            {bstate : ChainState} {caddr} {cstate : State} :
    contract_state bstate caddr = Some cstate ->
    reachable bstate ->
    exists (wc : WeakContract),
      env_contracts bstate caddr = Some wc.
  Proof.
    intros deployed_state [trace].
    trace_induction.
    destruct_chain_step; try rewrite_environment_equiv.
    - cbn in *. specialize_hypotheses. destruct IH as (wc & deployed). 
      exists wc. rewrite_environment_equiv; auto.
    - (* valid *)
      generalize dependent deployed_state.
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
    (* ChainTraceProperty.action_trace_induction_intermidiate.   *)
      intros deployed_state.
      destruct_action_eval.
      + rewrite_environment_equiv. cbn in *. specialize_hypotheses. destruct IH0 as (wc & deployed).
        exists wc. rewrite_environment_equiv; auto. 
      + rewrite_environment_equiv. cbn in *. 
        destruct_address_eq; subst. 
        * exists wc. rewrite_environment_equiv. cbn. rewrite address_eq_refl. auto. 
        * specialize_hypotheses. destruct IH0 as (wc' & deployed).
          exists wc'. rewrite_environment_equiv; cbn. rewrite address_eq_ne; auto. 
      + 
        destruct (address_eqb_spec caddr to_addr); subst.
        * exists wc. rewrite_environment_equiv. cbn. auto.
        * rewrite_environment_equiv. cbn in *. rewrite address_eq_ne in deployed_state; auto. 
          specialize_hypotheses. destruct IH0 as (wc' & deployed').
          exists wc'. rewrite_environment_equiv; auto.  
    - cbn in *. specialize_hypotheses. destruct IH as (wc & deployed). 
      exists wc. rewrite_environment_equiv; auto.
  Qed.

  Lemma deployed_state_wc_typed_action_trace
            {State : Type} `{Serializable State}
            {bstate : ChainState} {caddr} {cstate : State} :
    contract_state bstate caddr = Some cstate ->
    reachable_action_trace bstate ->
    exists (wc : WeakContract),
      env_contracts bstate caddr = Some wc.
  Proof.
    intros deployed_state (origin & reach & [trace]).
    action_trace_induction.
    { eapply deployed_state_wc_typed; eauto. }
    destruct_action_eval.
    + rewrite_environment_equiv. cbn in *. specialize_hypotheses. destruct IH as (wc & deployed).
      exists wc. rewrite_environment_equiv; auto. 
    + rewrite_environment_equiv. cbn in *. 
      destruct_address_eq; subst. 
      * exists wc. rewrite_environment_equiv. cbn. rewrite address_eq_refl. auto. 
      * specialize_hypotheses. destruct IH as (wc' & deployed).
        exists wc'. rewrite_environment_equiv; cbn. rewrite address_eq_ne; auto. 
    + 
      destruct (address_eqb_spec caddr to_addr); subst.
      * exists wc. rewrite_environment_equiv. cbn. auto.
      * rewrite_environment_equiv. cbn in *. rewrite address_eq_ne in deployed_state; auto. 
        specialize_hypotheses. destruct IH as (wc' & deployed').
        exists wc'. rewrite_environment_equiv; auto.  
  Qed.

  Lemma deployed_contract_state_typed_action_trace
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {bstate : ChainState}
            {caddr} :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    reachable_action_trace bstate ->
    exists (cstate : State),
      contract_state bstate caddr = Some cstate.
  Proof.
    intros contract_deployed (from & [trace] & [action_trace]). 
    action_trace_induction. 
    {
      (* base *)
      specialize (deployed_contract_state_typed contract_deployed) as (cstate & deployed_state); auto.
      constructor; auto. 
      exists cstate; auto.
    }
    specialize_hypotheses.
    destruct_action_eval; subst; rewrite_environment_equiv; cbn in *.
    - (* Transfer, use IH *)
      specialize_hypotheses. destruct IH as (cstate & deployed_state).
      exists cstate. rewrite_environment_equiv. auto.
    - (* Deployment *)
      destruct_address_eq; subst; auto. 
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_init_strong ltac:(eassumption))
        as [setup_strong [result_strong [? [<- init]]]].
      exists result_strong. 
      rewrite_environment_equiv. cbn. rewrite address_eq_refl. 
      rewrite deserialize_serialize; auto. 
      specialize_hypotheses. 
      destruct IH  as (cstate & deployed_state). 
      exists cstate. rewrite_environment_equiv. cbn. 
      rewrite address_eq_ne; auto.
    - (* Call *)
      destruct (address_eqb_spec caddr to_addr); subst; auto.
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_receive_strong ltac:(eassumption))
        as [state_strong [msg_strong [resp_state_strong [? [? [<- receive]]]]]].
      exists resp_state_strong.
      rewrite_environment_equiv. cbn. rewrite address_eq_refl, deserialize_serialize; auto.
      specialize_hypotheses. 
      destruct IH  as (cstate & deployed_state'). 
      exists cstate. rewrite_environment_equiv. cbn. 
      rewrite address_eq_ne; auto.
  Qed.

  Lemma incoming_calls_typed {Setup Msg State Error : Type}
        `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
        {contract : Contract Setup Msg State Error}
        {caddr} {bstate} (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists inc_calls, 
      incoming_calls Msg trace caddr = Some inc_calls.
  Proof.
    intros * deployed.
    trace_induction; cbn.  
    destruct_chain_step; try rewrite_environment_equiv; cbn in *. 
    - specialize_hypotheses. destruct IH as (inc_calls & IH). eexists; eauto.
    - enough (A : forall st (action_trace : ActionChainTrace mid st),
      env_contracts st caddr = Some (contract : WeakContract) ->
      exists inc_calls',
        act_trace_incoming_calls Msg action_trace caddr = Some inc_calls').
      { 
        destruct (env_contracts mid caddr) eqn:Hdeployed. 
        - assert (reach_at : reachable_in_action_trace mid to). 
          { split; auto. constructor; auto. } 
          specialize (weak_contract_preserve_action_trace reach_at Hdeployed) as Hpreserve; auto. 
          inversion_deployed_contract. 
          specialize_hypotheses. 
          destruct IH as (inc_calls & IH).
          destruct A as (inc_calls' & Hat). 
          rewrite Hat, IH. eexists; eauto.
        - rewrite (undeployed_contract_no_in_calls caddr mid); auto. 
          destruct (A to action_trace) as (inc_calls' & Hat); auto. 
          rewrite Hat. eexists; eauto.
       }
      intros * deployed_st.
      remember mid; induction action_trace0; subst.
      exists []. cbn. auto. 
      specialize_hypotheses. 
      destruct_action_chain_step. 
      destruct_action_eval; try rewrite_environment_equiv; subst; cbn in *.
      + specialize_hypotheses.
        destruct (IHaction_trace0) as (inc_calls' & Hat). 
        exists inc_calls'; auto.
      + destruct_address_eq; subst. 
        * rewrite (at_undeployed_contract_no_in_calls to_addr mid mid0 action_trace0); auto. 
          eexists; eauto. 
          constructor; auto. 
        * specialize_hypotheses. 
          destruct (IHaction_trace0) as (inc_calls' & Hat). 
          exists inc_calls'; auto. 
      + specialize_hypotheses. 
        destruct (IHaction_trace0) as (inc_calls' & Hat).
        rewrite Hat.
        destruct_address_eq; subst.
        * 
          inversion_deployed_contract.  
          apply wc_receive_strong in receive_some as (? & msg_strong & ? & ? & Hmsg & _). 
          destruct msg_strong. 
          -- destruct msg. cbn in Hmsg. rewrite Hmsg. 
            eexists; eauto. 
            cbn in Hmsg. congruence. 
          -- subst. eexists; eauto. 
        * eexists; eauto.
    - specialize_hypotheses. destruct IH as (inc_calls & IH). eexists; eauto. 
  Qed. 

  Lemma incoming_calls_typed' {Setup Msg State Error : Type}
        `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
        {contract : Contract Setup Msg State Error}
        {caddr} {bstate bstate'} (trace : ChainTrace bstate bstate') :
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) -> 
    exists inc_calls, 
      incoming_calls Msg trace caddr = Some inc_calls.
  Proof.
    intros * reach deployed.
    remember bstate; induction trace; subst.
    cbn. eexists; eauto.  
    destruct_chain_step; try rewrite_environment_equiv; cbn in *. 
    - specialize_hypotheses. destruct IHtrace as (inc_calls & IH). eexists; eauto.
    - enough (A : forall st (action_trace : ActionChainTrace mid st),
      env_contracts st caddr = Some (contract : WeakContract) ->
      exists inc_calls',
        act_trace_incoming_calls Msg action_trace caddr = Some inc_calls').
      {
        specialize (contract_preserve reach deployed trace) as (deployed_mid & cstate_mid & deployed_state_mid).
        assert (reach_at : reachable_in_action_trace mid to). 
        { split; auto. eapply reachable_trans; eauto. } 
        specialize (contract_preserve_action_trace reach_at deployed_mid) 
          as (deployed_to & _).
        specialize_hypotheses. 
        destruct IHtrace as (inc_calls & IH).
        destruct A as (inc_calls' & Hat). 
        rewrite Hat, IH. eexists; eauto.
       }
      intros * deployed_st.
      remember mid; induction action_trace0; subst.
      exists []. cbn. auto. 
      specialize_hypotheses. 
      destruct_action_chain_step. 
      destruct_action_eval; try rewrite_environment_equiv; subst; cbn in *.
      + specialize_hypotheses.
        destruct (IHaction_trace0) as (inc_calls' & Hat). 
        exists inc_calls'; auto.
      + destruct_address_eq; subst. 
        * rewrite (at_undeployed_contract_no_in_calls to_addr mid mid0 action_trace0); auto. 
          eexists; eauto. eapply reachable_trans; eauto. 
        * specialize_hypotheses. 
          destruct (IHaction_trace0) as (inc_calls' & Hat). 
          exists inc_calls'; auto. 
      + specialize_hypotheses. 
        destruct (IHaction_trace0) as (inc_calls' & Hat).
        rewrite Hat.
        destruct_address_eq; subst.
        * 
          inversion_deployed_contract.  
          apply wc_receive_strong in receive_some as (? & msg_strong & ? & ? & Hmsg & _). 
          destruct msg_strong. 
          -- destruct msg. cbn in Hmsg. rewrite Hmsg. 
            eexists; eauto. 
            cbn in Hmsg. congruence. 
          -- subst. eexists; eauto. 
        * eexists; eauto.
    - specialize_hypotheses. destruct IHtrace as (inc_calls & IH). eexists; eauto. 
  Qed. 

  Lemma incoming_calls_app {Msg : Type} `{Serializable Msg}
        (* {contract : Contract Setup Msg State Error} *)
        {caddr} {st1 st2 st3} {trace12 : ChainTrace st1 st2} {trace23 : ChainTrace st2 st3}
        (inc_calls1 inc_calls2 : list (ContractCallInfo Msg)) : 
    incoming_calls Msg trace12 caddr = Some inc_calls1 ->
    incoming_calls Msg trace23 caddr = Some inc_calls2 ->
    incoming_calls Msg (clist_app trace12 trace23) caddr = Some (inc_calls2 ++ inc_calls1).
  Proof.
    (* remember st1; induction trace12; subst; intros. 
    cbn in *. inversion_subst H0. rewrite app_clnil_l, app_nil_r. auto.  *)
    generalize dependent inc_calls2.
    generalize dependent inc_calls1.
    remember st2; induction trace23; subst; intros. 
    cbn in *. inversion_subst H1. auto. 
    cbn. 
    destruct_chain_step; auto. cbn in *. 
    destruct (act_trace_incoming_calls Msg action_trace caddr); try congruence. 
    destruct (incoming_calls Msg trace23 caddr) eqn:H23; try congruence. 
    erewrite IHtrace23; eauto. inversion_subst H1. now rewrite app_assoc.
  Qed. 

  
  Definition stream_to_trace 
      (bstate : ChainState)
      (trace : ChainTrace empty_state bstate)
      (str : ChainStream)
      (Hpath : path str)
      (Hstart : Str_nth 0 str = bstate) 
      (n : nat) : ChainTrace empty_state (Str_nth n str).
  Proof.
    induction n.
    rewrite Hstart; auto. 
    unfold path in Hpath. eapply (snoc IHn).
    (* destruct (Hpath n) as [step]. *)
  Abort.

End MyBuildUtils.

Local Ltac evaluate_receive_one_step :=
  lazymatch goal with
  | |- ?lhs = Ok ?rhs =>
      lazymatch lhs with
      | context[match ?g with | Ok _ => _ | Err _ => _ end] =>
          
          let A :=
            lazymatch type of g with
            | result ?A _ => A
            | ResultMonad.result ?A _ => A
            end 
          in
          lazymatch g with
          | throwIf ?b ?e =>
              cut (b = false);
              [ let Hb := fresh "Hb" in
                intro Hb; rewrite Hb; cbn [throwIf] | ]
          | _ => 
            let x := fresh "x" in
            evar (x : A);
            cut (g = Ok x);
            let Hok := fresh "Hok" in
            intro Hok; rewrite Hok; cbn
          end          
      end
  end.


Ltac evaluate_receive := 
  match goal with
      | |- Blockchain_modify_2.receive ?contract ?chain ?ctx ?cstate ?msg = Ok (?new_cstate, ?new_acts) =>
          cbn;
          repeat evaluate_receive_one_step; 
          auto
      end.
