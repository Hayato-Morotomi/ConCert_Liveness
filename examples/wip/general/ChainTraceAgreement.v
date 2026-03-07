From ConCert.Execution Require Import Blockchain.
From ConCert.Examples.Wip.General Require Import Blockchain_modify_2.

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify_2.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import ContractCommon_modify_2.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ChainedList.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Module Orig := ConCert.Execution.Blockchain.
Module Mod  := Blockchain_modify_2.







Section ChainTraceAgreement.
  Context {BaseO : Orig.ChainBase}.

  Local Instance BaseM : Mod.ChainBase :=
    {|
      Mod.Address := Orig.Address;
      Mod.address_eqb := Orig.address_eqb;
      Mod.address_eqb_spec := Orig.address_eqb_spec;
      Mod.address_eqdec := Orig.address_eqdec;
      Mod.address_countable := Orig.address_countable;
      Mod.address_serializable := Orig.address_serializable;
      Mod.address_is_contract := Orig.address_is_contract;
    |}.

  Section EraseLayer.
    
    Context (erase_wc : Mod.WeakContract -> Orig.WeakContract).

    
    Definition erase_chain (c : Mod.Chain) : Orig.Chain :=
      {|
        Orig.chain_height := Mod.chain_height c;
        Orig.current_slot := Mod.current_slot c;
        Orig.finalized_height := Mod.finalized_height c;
      |}.

    
    Definition erase_ctx (ctx : Mod.ContractCallContext) : Orig.ContractCallContext :=
      {|
        Orig.ctx_origin := Mod.ctx_origin ctx;
        Orig.ctx_from := Mod.ctx_from ctx;
        Orig.ctx_contract_address := Mod.ctx_contract_address ctx;
        Orig.ctx_contract_balance := Mod.ctx_contract_balance ctx;
        Orig.ctx_amount := Mod.ctx_amount ctx;
      |}.

    
    Definition erase_ab (ab : Mod.ActionBody) : Orig.ActionBody :=
      match ab with
      | Mod.act_transfer to amount => Orig.act_transfer to amount
      | Mod.act_call to amount msg => Orig.act_call to amount msg
      | Mod.act_deploy amount wc setup => Orig.act_deploy amount (erase_wc wc) setup
      end.

    
    Definition erase_act (a : Mod.Action) : Orig.Action :=
      {|
        Orig.act_origin := Mod.act_origin a;
        Orig.act_from := Mod.act_from a;
        Orig.act_body := erase_ab (Mod.act_body a);
      |}.

    
    Definition erase_env (e : Mod.Environment) : Orig.Environment :=
      {|
        Orig.env_chain := erase_chain (Mod.env_chain e);
        Orig.env_account_balances := Mod.env_account_balances e;
        Orig.env_contracts := fun a => option_map erase_wc (Mod.env_contracts e a);
        Orig.env_contract_states := Mod.env_contract_states e;
      |}.

    
    Definition erase_state (st : Mod.ChainState) : Orig.ChainState :=
      {|
        Orig.chain_state_env := erase_env (Mod.chain_state_env st);
        Orig.chain_state_queue := map erase_act (Mod.chain_state_queue st);
      |}.

(* Mod.BlockHeader -> Orig.BlockHeader *)
Definition erase_header (h : Mod.BlockHeader) : Orig.BlockHeader :=
  {|
    Orig.block_height := Mod.block_height h;
    Orig.block_slot := Mod.block_slot h;
    Orig.block_finalized_height := Mod.block_finalized_height h;
    Orig.block_reward := Mod.block_reward h;
    Orig.block_creator := Mod.block_creator h;
  |}.

  Lemma IsValidNextBlock_sound (h : Mod.BlockHeader) (c : Mod.Chain) :
    Mod.IsValidNextBlock h c ->
    Orig.IsValidNextBlock (erase_header h) (erase_chain c).
  Proof.
    intros H; destruct H as [vh vs vfh vc vr].
    refine
      {|
        Orig.valid_height := _;
        Orig.valid_slot := _;
        Orig.valid_finalized_height := _;
        Orig.valid_creator := _;
        Orig.valid_reward := _;
      |};
      cbn [erase_header erase_chain] in *; assumption.
  Qed.

    
    Local Coercion erase_state : Mod.ChainState >-> Orig.ChainState.
    Local Coercion erase_env   : Mod.Environment >-> Orig.Environment.
    Local Coercion erase_act   : Mod.Action >-> Orig.Action.

  Lemma act_is_from_account_sound (a : Mod.Action) :
    Mod.act_is_from_account a ->
    Orig.act_is_from_account (erase_act a).
  Proof.
    unfold Mod.act_is_from_account, Orig.act_is_from_account.
    cbn [erase_act]; auto.
  Qed.

  Lemma act_origin_is_eq_from_sound (a : Mod.Action) :
    Mod.act_origin_is_eq_from a ->
    Orig.act_origin_is_eq_from (erase_act a).
  Proof.
    unfold Mod.act_origin_is_eq_from, Orig.act_origin_is_eq_from.
    cbn [erase_act]; auto.
  Qed.

  Lemma Forall_act_is_from_account_sound (acts : list Mod.Action) :
    Forall Mod.act_is_from_account acts ->
    Forall Orig.act_is_from_account (map erase_act acts).
  Proof.
    induction 1; cbn; constructor; auto using act_is_from_account_sound.
  Qed.

  Lemma Forall_act_origin_is_eq_from_sound (acts : list Mod.Action) :
    Forall Mod.act_origin_is_eq_from acts ->
    Forall Orig.act_origin_is_eq_from (map erase_act acts).
  Proof.
    induction 1; cbn; constructor; auto using act_origin_is_eq_from_sound.
  Qed.

  Lemma EnvironmentEquiv_sound (e1 e2 : Mod.Environment) :
    Mod.EnvironmentEquiv e1 e2 ->
    Orig.EnvironmentEquiv (erase_env e1) (erase_env e2).
  Proof.
    intro Heq; destruct Heq as [Hc Hb Hcon Hst].
    apply Orig.build_env_equiv; cbn.
    - now rewrite Hc.
    - intro a; exact (Hb a).
    - intro a; now rewrite (Hcon a).
    - intro a; exact (Hst a).
  Qed.

  


  Lemma EnvironmentEquiv_erase_add_new_block (h : Mod.BlockHeader) (e : Mod.Environment) :
    Orig.EnvironmentEquiv (erase_env (Mod.add_new_block_to_env h e))
                          (Orig.add_new_block_to_env (erase_header h) (erase_env e)).
  Proof.
    apply Orig.build_env_equiv; cbn; try reflexivity.
  Qed.

    





    Context
      (ActionEvaluation_sound :
         forall (prev : Mod.Environment) (act : Mod.Action)
                (new : Mod.Environment) (new_acts : list Mod.Action),
           Mod.ActionEvaluation prev act new new_acts ->
           Orig.ActionEvaluation (erase_env prev) (erase_act act)
                                 (erase_env new) (map erase_act new_acts)).

    





    Lemma ActionChainStep_to_OrigChainStep (st1 st2 : Mod.ChainState) :
      Mod.ActionChainStep st1 st2 ->
      Orig.ChainStep st1 st2.
    Proof.
      intro H.
      inversion H as [act acts new_acts Hq Heval Hq']; subst.
      eapply Orig.step_action
        with (act := erase_act act)
             (acts := map erase_act acts)
             (new_acts := map erase_act new_acts).
      - 
        cbn. rewrite Hq. cbn. reflexivity.
      - 
        exact (ActionEvaluation_sound st1 act st2 new_acts Heval).
      - 
        cbn. rewrite Hq'. now rewrite map_app.
    Qed.

  Lemma ActionChainTrace_to_OrigChainTrace (st1 st2 : Mod.ChainState) :
    Mod.ActionChainTrace st1 st2 ->
    Orig.ChainTrace st1 st2.
  Proof.
    intro action_trace. remember st1; induction action_trace; subst.
    constructor. 
    specialize_hypotheses. 
    apply ActionChainStep_to_OrigChainStep in l.
    apply (snoc IHaction_trace l).
  Qed.

  



  Lemma ModChainStep_to_OrigChainTrace (st1 st2 : Mod.ChainState) :
    Mod.reachable st1 -> 
    Mod.ChainStep st1 st2 ->
    Orig.ChainTrace st1 st2. 
  Proof.
    intros reach step. 
    destruct_chain_step. 
    - enough (Orig.ChainStep st1 st2) as step_orig.
      { apply (snoc clnil step_orig). }
      apply (f_equal (map erase_act)) in queue_prev. cbn in queue_prev.
      eapply (Orig.step_block) with (header := erase_header header); eauto.
      + (* 2/5: IsValidNextBlock *)
        change (Orig.IsValidNextBlock (erase_header header)
                (erase_chain (Mod.env_chain (Mod.chain_state_env st1)))).
        apply IsValidNextBlock_sound. exact valid_header.
      + (* 3/5: Forall act_is_from_account *)
        change (Forall Orig.act_is_from_account
                (map erase_act (Mod.chain_state_queue st2))).
        apply Forall_act_is_from_account_sound. exact acts_from_accs.
      + (* 4/5: Forall act_origin_is_eq_from *)
        change (Forall Orig.act_origin_is_eq_from
                (map erase_act (Mod.chain_state_queue st2))).
        apply Forall_act_origin_is_eq_from_sound. exact origin_correct.
      + (* 5/5: EnvironmentEquiv *)
        
        eapply RelationClasses.transitivity.
        * exact (EnvironmentEquiv_sound _ _ env_eq).
        * apply EnvironmentEquiv_erase_add_new_block.
    - apply ActionChainTrace_to_OrigChainTrace; auto. 
    - specialize (queue_from_account st1 reach) as from_accs. 
      rewrite_queue.
      apply Forall_cons_iff in from_accs as (from_acc & _).
      enough (Orig.ChainStep st1 st2) as step_orig. 
      { apply (snoc clnil step_orig). }
      apply (f_equal (map erase_act)) in queue_prev. 
      apply (f_equal (map erase_act)) in queue_new. cbn in *.
      eapply Orig.step_action_invalid; eauto.
      + exact (EnvironmentEquiv_sound _ _ env_eq).
      + 
        enough (
         (forall bstate new_acts, 
          Orig.ActionEvaluation st1 act bstate new_acts -> 
                                              False) ->
         (forall bstate,
          bstate.(Mod.chain_state_queue) = acts ->
          Mod.ActionChainTrace st1 bstate -> 
                                               False) 
        ). 
        intros * no_eval.
        eapply H.
        (* eapply (no_action_trace).  *)
         
      all : admit. 
  Admitted.

  Lemma ModChainTrace_to_OrigChainTrace (st1 st2 : Mod.ChainState) :
    Mod.reachable st1 -> 
    Mod.ChainTrace st1 st2 ->
    Orig.ChainTrace st1 st2. 
  Proof.
    intros reach trace. remember st1; induction trace; subst. 
    constructor. 
    specialize_hypotheses. apply ModChainStep_to_OrigChainTrace in l. 
    apply (clist_app IHtrace l). 
    eapply (reachable_trans); eauto. 
  Qed.  

    








  End EraseLayer.
End ChainTraceAgreement.