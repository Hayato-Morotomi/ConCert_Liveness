From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.

Local Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq
  end.

Local Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

Section ChainStepDetermin.
  Context {BaseTypes : ChainBase}.

  Lemma action_evaluation_pre_equiv
        (pre pre' post : Environment)
        (act : Action)
        (new_acts : list Action) :
    EnvironmentEquiv pre pre' ->
    ActionEvaluation pre act post new_acts ->
    ActionEvaluation pre' act post new_acts.
  Proof.
    intros Hpre Heval.
    destruct Heval as
      [limit origin from_addr to_addr amount g g0 l e e0 e1 e2
      | limit origin from_addr to_addr amount wc setup state g g0 l H e e0 e1 e2 e3
      | limit origin from_addr to_addr amount wc msg prev_state new_state resp_acts
          g g0 l e e0 e1 e2 e3 e4].
    - eapply eval_transfer; eauto; try now rewrite <- Hpre.
    - assert (Hiff : forall x, fresh_address pre x <-> fresh_address pre' x).
      { intros x. unfold fresh_address. now rewrite Hpre. }
      assert (H' : exists x, fresh_address pre' x).
      { destruct H as [x Hx]. exists x. now apply Hiff. }
      assert (l' : (amount <= env_account_balances pre' from_addr)%Z)
        by now rewrite <- Hpre.
      apply (eval_deploy limit origin from_addr to_addr amount wc setup state
               g g0 l' H').
      + rewrite e. now apply countable.choose_proper.
      + exact e0.
      + now rewrite <- Hpre.
      + now rewrite <- Hpre.
      + exact e3.
    - eapply (eval_call limit origin from_addr to_addr amount wc msg prev_state new_state resp_acts);
        eauto; try now rewrite <- Hpre.
  Qed.

  Lemma action_evaluation_deterministic
        (prev : ChainState)
        (act : Action)
        (next1 next2 : ChainState)
        (acts1 acts2 : list Action) :
    reachable prev ->
    ActionEvaluation prev act next1 acts1 ->
    ActionEvaluation prev act next2 acts2 ->
    acts1 = acts2 /\ EnvironmentEquiv next1 next2.
  Proof.
    intros Hreach Ev1 Ev2.
    destruct Ev1 as
      [l1 o1 f1 t1 amount1
          Hlim1 Hnonneg1 Hle1 Hto_account1 Hact1 Henv1 Hacts1
      | l1 o1 f1 t1 amount1 wc1 setup1 state1
          Hlim1 Hnonneg1 Hle1 Hto_contract1 Hnone1 Hact1 Hinit1 Henv1 Hacts1
      | l1 o1 f1 t1 amount1 wc1 msg1 prev_state1 new_state1 resp_acts1
          Hlim1 Hnonneg1 Hle1 Hcontract1 Hstate1 Hact1 Hreceive1 Hacts1 Henv1];
    destruct Ev2 as
      [l2 o2 f2 t2 amount2
          Hlim2 Hnonneg2 Hle2 Hto_account2 Hact2 Henv2 Hacts2
      | l2 o2 f2 t2 amount2 wc2 setup2 state2
          Hlim2 Hnonneg2 Hle2 Hto_contract2 Hnone2 Hact2 Hinit2 Henv2 Hacts2
      | l2 o2 f2 t2 amount2 wc2 msg2 prev_state2 new_state2 resp_acts2
          Hlim2 Hnonneg2 Hle2 Hcontract2 Hstate2 Hact2 Hreceive2 Hacts2 Henv2];
      subst act.

    - inversion Hact2; subst; clear Hact2.
      split; [reflexivity|].
      etransitivity; [exact Henv1|].
      symmetry; exact Henv2.

    - inversion Hact2; subst; congruence.

    - destruct msg2 as [msg2|].
      + inversion Hact2; subst; congruence.
      + inversion Hact2; subst; clear Hact2.
        pose proof (contract_addr_format t2 wc2 Hreach Hcontract2).
        congruence.

    - inversion Hact2; subst; congruence.

    - inversion Hact2; subst; clear Hact2.
      split; [reflexivity|].
      (* the deployed address is countable.choose of the fresh addresses;
         any two proofs of existence give the same address (choose_pi) *)
      rewrite (countable.choose_pi _ Hto_contract1 Hto_contract2) in *.
      assert (state1 = state2) by congruence.
      subst state2.
      etransitivity; [exact Henv1|].
      symmetry; exact Henv2.

    - destruct msg2 as [msg2|];
        inversion Hact2; subst; congruence.

    - destruct msg1 as [msg1|].
      + inversion Hact2; subst; congruence.
      + inversion Hact2; subst; clear Hact2.
        pose proof (contract_addr_format t2 wc1 Hreach Hcontract1).
        congruence.

    - destruct msg1 as [msg1|];
        inversion Hact2; subst; congruence.

    - destruct msg1 as [msg1|], msg2 as [msg2|];
        try solve [inversion Hact2; subst; congruence].
      + inversion Hact2; subst; clear Hact2.
        replace wc2 with wc1 in * by congruence.
        replace prev_state2 with prev_state1 in * by congruence.
        assert (Hctx_bal :
          env_account_balances next1 t2 =
          env_account_balances next2 t2).
        {
          rewrite Henv1.
          rewrite Henv2.
          cbn.
          reflexivity.
        }
        rewrite <- Hctx_bal in Hreceive2.
        rewrite Hreceive1 in Hreceive2.
        injection Hreceive2 as Hpair.
        inversion Hpair; subst.
        split; [reflexivity|].
        etransitivity; [exact Henv1|].
        symmetry; exact Henv2.

      + inversion Hact2; subst; clear Hact2.
        replace wc2 with wc1 in * by congruence.
        replace prev_state2 with prev_state1 in * by congruence.
        assert (Hctx_bal :
          env_account_balances next1 t2 =
          env_account_balances next2 t2).
        {
          rewrite Henv1.
          rewrite Henv2.
          cbn.
          reflexivity.
        }
        rewrite <- Hctx_bal in Hreceive2.
        rewrite Hreceive1 in Hreceive2.
        injection Hreceive2 as Hpair.
        inversion Hpair; subst.
        split; [reflexivity|].
        etransitivity; [exact Henv1|].
        symmetry; exact Henv2.
  Qed.

  Lemma action_evaluation_deterministic_strong
        {prev1 prev2 : ChainState}
        {act : Action}
        {next1 next2 : ChainState}
        {acts1 acts2 : list Action} :
    ActionEvaluation prev1 act next1 acts1 ->
    ActionEvaluation prev2 act next2 acts2 ->
    reachable prev1 ->
    reachable prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    acts1 = acts2 /\ EnvironmentEquiv next1 next2.
  Proof.
    intros Ev1 Ev2 Hreach1 Hreach2 Hequiv Hq.
    assert (Hequiv_sym : EnvironmentEquiv prev2 prev1).
    { symmetry. exact Hequiv. }
    pose proof
      (action_evaluation_pre_equiv prev2 prev1 next2 act acts2
         Hequiv_sym Ev2)
      as Ev2_on_prev1.
    eapply (action_evaluation_deterministic prev1 act next1 next2 acts1 acts2);
      eauto.
  Qed.

Section ActionTraceUtils.

  Lemma action_trace_step_trace {from mid to} :
    ActionChainStep from mid ->
    ActionChainTrace mid to ->
    inhabited (ActionChainTrace from to).
  Proof.
    intros step trace.
    revert from step.
    induction trace as [|mid mid' to trace IH step_tail];
      intros from step.
    - constructor. exact (snoc clnil step).
    - destruct (IH from step) as [trace0].
      constructor. exact (snoc trace0 step_tail).
  Qed.

  Lemma action_trace_step {from to} :
    ActionChainTrace from to ->
    from = to \/
    exists mid,
      inhabited (ActionChainStep from mid) /\
      inhabited (ActionChainTrace mid to).
  Proof.
    intros trace.
    induction trace as [|from mid to trace IH step].
    - left; reflexivity.
    - destruct IH as [Hsame | (mid' & [step'] & [trace'])].
      + subst mid.
        right. exists to. split.
        * constructor. exact step.
        * constructor. apply clnil.
      + right. exists mid'. split.
        * constructor; exact step'.
        * constructor. eapply snoc; eauto.
  Qed.

  Lemma action_trace_trans {from mid to} :
    ActionChainTrace from mid ->
    ActionChainTrace mid to ->
    inhabited (ActionChainTrace from to).
  Proof.
    intros tr1 tr2.
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  Lemma reachable_action_trace_refl {st} :
    reachable st ->
    reachable_action_trace st st.
  Proof.
    intros Hreach.
    unfold reachable_action_trace.
    split; auto.
    constructor; apply clnil.
  Qed.

  Lemma reachable_action_trace_trans {from st st'} :
    reachable_action_trace from st ->
    ActionChainTrace st st' ->
    reachable_action_trace from st'.
  Proof.
    unfold reachable_action_trace.
    intros (Hreach & [trace1]) trace2.
    split; auto.
    constructor.
    now eapply ChainedList.clist_app.
  Qed.

  Lemma reachable_action_trace_step {from st st'} :
    reachable_action_trace from st ->
    ActionChainStep st st' ->
    reachable_action_trace from st'.
  Proof.
    unfold reachable_action_trace.
    intros (Hreach & [trace]) step.
    split; auto.
    constructor.
    exact (snoc trace step).
  Qed.

  Lemma contract_addr_format_action_trace
        {from to : ChainState}
        (addr : Address)
        (wc : WeakContract) :
    reachable from ->
    ActionChainTrace from to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros Hreach trace.
    induction trace as [|from mid to trace IH step]; intros Hcontract.
    - eapply contract_addr_format; eauto.
    - destruct step as [act acts new_acts Hqueue Heval Hqueue_next].
      destruct_action_eval; subst; rewrite_environment_equiv in *; cbn in *; eauto.
      destruct_address_eq; subst; cbn in *; eauto.
  Qed.

  Lemma contract_addr_format_in_action_trace
        {from to : ChainState}
        (addr : Address)
        (wc : WeakContract) :
    reachable_action_trace from to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros (Hreach & [trace]) Hcontract.
    eapply contract_addr_format_action_trace; eauto.
  Qed.

  Lemma emitted_acts_from_contract_in_action_trace
        {from bstate : ChainState}
        {act : Action}
        {acts : list Action}
        {next_env : Environment}
        {new_acts : list Action} :
    reachable_action_trace from bstate ->
    bstate.(chain_state_queue) = act :: acts ->
    ActionEvaluation bstate act next_env new_acts ->
    Forall act_is_from_contract new_acts.
  Proof.
    intros Hreach Hqueue Heval.
    destruct_action_eval; subst; auto.
    apply All_Forall.Forall_map.
    unfold act_is_from_contract. cbn.
    apply Forall_forall.
    intros body _.
    eapply contract_addr_format_in_action_trace; eauto.
  Qed.

End ActionTraceUtils.

  Lemma eval_new_acts_from_contract_reachable
        (bstate : ChainState)
        act
        (new_env : Environment)
        new_acts :
    reachable bstate ->
    ActionEvaluation bstate act new_env new_acts ->
    Forall act_is_from_contract new_acts.
  Proof.
    intros Hreach Heval.
    destruct_action_eval; subst; auto.
    apply All_Forall.Forall_map.
    unfold act_is_from_contract. cbn.
    apply Forall_forall.
    intros body _.
    eapply contract_addr_format; eauto.
  Qed.

  Lemma action_evaluation_deterministic_in_action_trace
        {origin prev : ChainState}
        {act : Action}
        {next1 next2 : ChainState}
        {acts1 acts2 : list Action} :
    reachable_action_trace origin prev ->
    ActionEvaluation prev act next1 acts1 ->
    ActionEvaluation prev act next2 acts2 ->
    acts1 = acts2 /\ EnvironmentEquiv next1 next2.
  Proof.
    intros Hreach Ev1 Ev2.
    destruct Ev1 as
      [l1 o1 f1 t1 amount1
          Hlim1 Hnonneg1 Hle1 Hto_account1 Hact1 Henv1 Hacts1
      | l1 o1 f1 t1 amount1 wc1 setup1 state1
          Hlim1 Hnonneg1 Hle1 Hto_contract1 Hnone1 Hact1 Hinit1 Henv1 Hacts1
      | l1 o1 f1 t1 amount1 wc1 msg1 prev_state1 new_state1 resp_acts1
          Hlim1 Hnonneg1 Hle1 Hcontract1 Hstate1 Hact1 Hreceive1 Hacts1 Henv1];
    destruct Ev2 as
      [l2 o2 f2 t2 amount2
          Hlim2 Hnonneg2 Hle2 Hto_account2 Hact2 Henv2 Hacts2
      | l2 o2 f2 t2 amount2 wc2 setup2 state2
          Hlim2 Hnonneg2 Hle2 Hto_contract2 Hnone2 Hact2 Hinit2 Henv2 Hacts2
      | l2 o2 f2 t2 amount2 wc2 msg2 prev_state2 new_state2 resp_acts2
          Hlim2 Hnonneg2 Hle2 Hcontract2 Hstate2 Hact2 Hreceive2 Hacts2 Henv2];
      subst act.

    - inversion Hact2; subst; clear Hact2.
      split; [reflexivity|].
      etransitivity; [exact Henv1|].
      symmetry; exact Henv2.

    - inversion Hact2; subst; congruence.

    - destruct msg2 as [msg2|].
      + inversion Hact2; subst; congruence.
      + inversion Hact2; subst; clear Hact2.
        pose proof (contract_addr_format_in_action_trace t2 wc2 Hreach Hcontract2).
        congruence.

    - inversion Hact2; subst; congruence.

    - inversion Hact2; subst; clear Hact2.
      split; [reflexivity|].
      (* the deployed address is countable.choose of the fresh addresses;
         any two proofs of existence give the same address (choose_pi) *)
      rewrite (countable.choose_pi _ Hto_contract1 Hto_contract2) in *.
      assert (state1 = state2) by congruence.
      subst state2.
      etransitivity; [exact Henv1|].
      symmetry; exact Henv2.

    - destruct msg2 as [msg2|];
        inversion Hact2; subst; congruence.

    - destruct msg1 as [msg1|].
      + inversion Hact2; subst; congruence.
      + inversion Hact2; subst; clear Hact2.
        pose proof (contract_addr_format_in_action_trace t2 wc1 Hreach Hcontract1).
        congruence.

    - destruct msg1 as [msg1|];
        inversion Hact2; subst; congruence.

    - destruct msg1 as [msg1|], msg2 as [msg2|];
        try solve [inversion Hact2; subst; congruence].
      + inversion Hact2; subst; clear Hact2.
        replace wc2 with wc1 in * by congruence.
        replace prev_state2 with prev_state1 in * by congruence.
        assert (Hctx_bal :
          env_account_balances next1 t2 =
          env_account_balances next2 t2).
        {
          rewrite Henv1.
          rewrite Henv2.
          cbn.
          reflexivity.
        }
        rewrite <- Hctx_bal in Hreceive2.
        rewrite Hreceive1 in Hreceive2.
        injection Hreceive2 as Hpair.
        inversion Hpair; subst.
        split; [reflexivity|].
        etransitivity; [exact Henv1|].
        symmetry; exact Henv2.

      + inversion Hact2; subst; clear Hact2.
        replace wc2 with wc1 in * by congruence.
        replace prev_state2 with prev_state1 in * by congruence.
        assert (Hctx_bal :
          env_account_balances next1 t2 =
          env_account_balances next2 t2).
        {
          rewrite Henv1.
          rewrite Henv2.
          cbn.
          reflexivity.
        }
        rewrite <- Hctx_bal in Hreceive2.
        rewrite Hreceive1 in Hreceive2.
        injection Hreceive2 as Hpair.
        inversion Hpair; subst.
        split; [reflexivity|].
        etransitivity; [exact Henv1|].
        symmetry; exact Henv2.
  Qed.

  Lemma action_chain_step_deterministic_in_action_trace
        {origin prev next1 next2 : ChainState} :
    reachable_action_trace origin prev ->
    ActionChainStep prev next1 ->
    ActionChainStep prev next2 ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros Hreach Hstep1 Hstep2.
    destruct Hstep1 as [act1 acts1 new_acts1 Hq1 Heval1 Hnext1].
    destruct Hstep2 as [act2 acts2 new_acts2 Hq2 Heval2 Hnext2].
    rewrite Hq1 in Hq2.
    inversion Hq2; subst act2 acts2; clear Hq2.
    pose proof
      (action_evaluation_deterministic_in_action_trace
         Hreach Heval1 Heval2)
      as [Hnew_acts Henv].
    split; auto.
    rewrite Hnext1, Hnext2, Hnew_acts.
    reflexivity.
  Qed.

  Lemma action_chain_step_pre_equiv
        {prev1 prev2 next : ChainState} :
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    ActionChainStep prev1 next ->
    ActionChainStep prev2 next.
  Proof.
    intros Henv Hqueue Hstep.
    destruct Hstep as [act acts new_acts Hq Heval Hnext].
    eapply action_step.
    - rewrite <- Hqueue. exact Hq.
    - eapply action_evaluation_pre_equiv; eauto.
    - exact Hnext.
  Qed.

  Lemma action_trace_external_equiv
        {from1 to1 from2 : ChainState} :
    ActionChainTrace from1 to1 ->
    EnvironmentEquiv from1 from2 ->
    from1.(chain_state_queue) = from2.(chain_state_queue) ->
    exists to2,
      inhabited (ActionChainTrace from2 to2) /\
      EnvironmentEquiv to1 to2 /\
      to1.(chain_state_queue) = to2.(chain_state_queue).
  Proof.
    intros trace.
    generalize dependent from2.
    induction trace as [|from1 mid to1 trace IH step];
      intros from2 Henv Hqueue.
    - exists from2.
      split.
      + constructor; apply clnil.
      + split; assumption.
    - destruct (IH from2 Henv Hqueue)
        as (mid2 & [trace2] & Henv_mid & Hqueue_mid).
      pose proof
        (action_chain_step_pre_equiv Henv_mid Hqueue_mid step)
        as step2.
      exists to1.
      split.
      + constructor; eapply (snoc trace2 step2).
      + split; reflexivity.
  Qed.

  Lemma action_trace_no_branch :
    forall {origin st st1 st2 : ChainState}
           (trace1 : ActionChainTrace st st1)
           (trace2 : ActionChainTrace st st2),
      reachable_action_trace origin st ->
      (exists st2' (trace12 : ActionChainTrace st1 st2'),
          EnvironmentEquiv st2 st2' /\
          st2.(chain_state_queue) = st2'.(chain_state_queue)) \/
      (exists st1' (trace21 : ActionChainTrace st2 st1'),
          EnvironmentEquiv st1 st1' /\
          st1.(chain_state_queue) = st1'.(chain_state_queue)).
  Proof.
    intros origin st st1 st2 trace1.
    generalize dependent st2.
    induction trace1 as [|st mid st1 trace1 IH step1];
      intros st2 trace2 Hreach.
    - left.
      exists st2, trace2.
      split; reflexivity.
    - specialize (IH st2 trace2 Hreach)
        as [(st2' & trace12 & Henv2 & Hqueue2)
            | (mid' & trace21 & Henv_mid & Hqueue_mid)].
      + destruct (action_trace_step trace12)
          as [Hsame | (next & [step12] & [trace_next])].
        * subst st2'.
          assert (Henv_mid_st2 : EnvironmentEquiv mid st2).
          { symmetry. exact Henv2. }
          assert (Hqueue_mid_st2 : mid.(chain_state_queue) = st2.(chain_state_queue)).
          { symmetry. exact Hqueue2. }
          pose proof
            (action_chain_step_pre_equiv Henv_mid_st2 Hqueue_mid_st2 step1)
            as step2.
          right.
          exists st1, (snoc clnil step2).
          split; reflexivity.
        * assert (Hreach_mid : reachable_action_trace origin mid).
          { eapply reachable_action_trace_trans; eauto. }
          pose proof
            (action_chain_step_deterministic_in_action_trace
               Hreach_mid step1 step12)
            as [Henv_next Hqueue_next].
          assert (Henv_next_sym : EnvironmentEquiv next st1).
          { symmetry. exact Henv_next. }
          destruct
            (action_trace_external_equiv
               trace_next Henv_next_sym (eq_sym Hqueue_next))
            as (st2'' & [trace_from_st1] & Henv_st2' & Hqueue_st2').
          left.
          exists st2'', trace_from_st1.
          split.
          -- etransitivity; [exact Henv2|exact Henv_st2'].
          -- etransitivity; [exact Hqueue2|exact Hqueue_st2'].
      + pose proof
          (action_chain_step_pre_equiv Henv_mid Hqueue_mid step1)
          as step2.
        right.
        exists st1, (snoc trace21 step2).
        split; reflexivity.
  Qed.

Section ListDropFromContract.
    Fixpoint list_drop {T : Type} (f : T -> bool) (l : list T) : list T :=
      match l with
      | [] => []
      | h :: t => if f h then list_drop f t else l
      end.

    Lemma list_drop_le {T : Type} f (l : list T) :
      length (list_drop f l) <= length l.
    Proof.
      induction l as [|h t IH]; cbn; [lia|].
      destruct (f h); cbn; lia.
    Qed.

    Lemma list_drop_app_le {T : Type} f (l1 l2 : list T) :
      length (list_drop f l2) <= length (list_drop f (l1 ++ l2)).
    Proof.
      induction l1 as [|h t IH]; cbn; [lia|].
      destruct (f h); cbn.
      - exact IH.
      - pose proof (list_drop_le f l2). rewrite length_app. lia.
    Qed.

    Definition list_drop_contract_action :=
      list_drop (fun act => address_is_contract act.(act_from)).

    Lemma no_drop_from_account acts :
      Forall act_is_from_account acts ->
      list_drop_contract_action acts = acts.
    Proof.
      destruct acts as [|a acts]; cbn; auto.
      intro H.
      apply Forall_cons_iff in H as [Ha _].
      unfold act_is_from_account in Ha.
      rewrite Ha.
      reflexivity.
    Qed.

    Lemma drop_from_contract new_acts acts :
      Forall act_is_from_contract new_acts ->
      list_drop_contract_action (new_acts ++ acts) =
      list_drop_contract_action acts.
    Proof.
      induction new_acts as [|a new_acts IH]; cbn; auto.
      intro H.
      apply Forall_cons_iff in H as [Ha Htail].
      unfold act_is_from_contract in Ha.
      rewrite Ha.
      apply IH.
      exact Htail.
    Qed.

    Lemma forall_list_drop acts :
      Forall act_is_from_account acts ->
      Forall act_is_from_account (list_drop_contract_action acts).
    Proof.
      destruct acts as [|a acts]; cbn; auto.
      intro H.
      apply Forall_cons_iff in H as [Ha Htail].
      unfold act_is_from_account in Ha.
      rewrite Ha.
      constructor; auto.
    Qed.

    Lemma list_drop_contract_app_le acts1 acts2 :
      length (list_drop_contract_action acts2) <=
      length (list_drop_contract_action (acts1 ++ acts2)).
    Proof.
      unfold list_drop_contract_action.
      apply list_drop_app_le.
    Qed.
End ListDropFromContract.

  Lemma chain_step_list_drop_contract_action_preserved
        prev_bstate next_bstate :
    reachable prev_bstate ->
    Forall act_is_from_account
      (list_drop_contract_action prev_bstate.(chain_state_queue)) ->
    ChainStep prev_bstate next_bstate ->
    Forall act_is_from_account
      (list_drop_contract_action next_bstate.(chain_state_queue)).
  Proof.
    intros Hreach Hdrop Hstep.
    destruct Hstep as
      [header Hqueue_prev Hvalid_header Hnext_accounts Horigin_eq Henv_eq
      | act acts new_acts finish_bstate Hqueue_prev Heval Hqueue_next
          Hact_account Htrace Hqueue_finish
      | act acts new_acts Hqueue_prev Heval Hqueue_next Hact_contract
      | act acts fail_bstate act' acts' Henv_eq Hqueue_prev Hqueue_next
          Hact_account Htrace Hqueue_fail Hno_eval].
    - rewrite no_drop_from_account by exact Hnext_accounts.
      exact Hnext_accounts.
    - rewrite Hqueue_prev in Hdrop.
      cbn in Hdrop.
      unfold act_is_from_account in Hact_account.
      rewrite Hact_account in Hdrop.
      inversion Hdrop as [|? ? _ Hacts_account]; subst.
      pose proof
        (eval_new_acts_from_contract_reachable
           prev_bstate act next_bstate new_acts Hreach Heval)
        as Hnew_contract.
      rewrite Hqueue_next.
      rewrite drop_from_contract by exact Hnew_contract.
      apply forall_list_drop.
      exact Hacts_account.
    - rewrite Hqueue_prev in Hdrop.
      cbn in Hdrop.
      unfold act_is_from_contract in Hact_contract.
      rewrite Hact_contract in Hdrop.
      pose proof
        (eval_new_acts_from_contract_reachable
           prev_bstate act next_bstate new_acts Hreach Heval)
        as Hnew_contract.
      rewrite Hqueue_next.
      rewrite drop_from_contract by exact Hnew_contract.
      exact Hdrop.
    - rewrite Hqueue_prev in Hdrop.
      cbn in Hdrop.
      unfold act_is_from_account in Hact_account.
      rewrite Hact_account in Hdrop.
      inversion Hdrop as [|? ? _ Hacts_account]; subst.
      apply Forall_cons_iff in Hdrop as (? & ?).
      apply forall_list_drop; auto.
  Qed.

  Lemma chain_trace_list_drop_contract_action_preserved
        from to :
    reachable from ->
    Forall act_is_from_account
      (list_drop_contract_action from.(chain_state_queue)) ->
    ChainTrace from to ->
    Forall act_is_from_account
      (list_drop_contract_action to.(chain_state_queue)).
  Proof.
    intros Hreach Hdrop trace.
    revert Hreach Hdrop.
    induction trace as [|from mid to trace IH step];
      intros Hreach Hdrop.
    - exact Hdrop.
    - assert (Hreach_mid : reachable mid).
      {
        destruct Hreach as [trace0].
        constructor.
        eapply ChainedList.clist_app; eauto.
      }
      eapply chain_step_list_drop_contract_action_preserved.
      + exact Hreach_mid.
      + apply IH; assumption.
      + exact step.
  Qed.

  Lemma reachable_list_drop_contract_action_queue st :
    reachable st ->
    Forall act_is_from_account
      (list_drop_contract_action st.(chain_state_queue)).
  Proof.
    intros Hreach.
    destruct Hreach as [trace].
    eapply chain_trace_list_drop_contract_action_preserved.
    - constructor. apply clnil.
    - cbn. constructor.
    - exact trace.
  Qed.

  Lemma reachable_queue_tail_accounts_from_account st act acts :
    reachable st ->
    st.(chain_state_queue) = act :: acts ->
    act_is_from_account act ->
    Forall act_is_from_account acts.
  Proof.
    intros Hreach Hqueue Hact_account.
    pose proof (reachable_list_drop_contract_action_queue st Hreach) as Hdrop.
    rewrite Hqueue in Hdrop.
    cbn in Hdrop.
    unfold act_is_from_account in Hact_account.
    rewrite Hact_account in Hdrop.
    inversion Hdrop; subst.
    assumption.
  Qed.

  Lemma list_drop_contract_action_cons_contract act acts :
    act_is_from_contract act ->
    list_drop_contract_action (act :: acts) =
    list_drop_contract_action acts.
  Proof.
    intro Hact_contract.
    unfold list_drop_contract_action.
    cbn.
    unfold act_is_from_contract in Hact_contract.
    rewrite Hact_contract.
    reflexivity.
  Qed.

  Lemma list_drop_contract_contradiction act acts :
    act :: acts <> list_drop_contract_action acts.
  Proof.
    intro Heq.
    pose proof
      (list_drop_le
         (fun act : Action => address_is_contract (act_from act))
         acts) as Hlen.
    apply (f_equal (@length Action)) in Heq.
    unfold list_drop_contract_action in Heq.
    cbn in Heq.
    lia.
  Qed.

  Lemma list_drop_contract_action_head_contract_neq act acts :
    act_is_from_contract act ->
    act :: acts <> list_drop_contract_action (act :: acts).
  Proof.
    intros Hact_contract Heq.
    rewrite list_drop_contract_action_cons_contract in Heq
      by exact Hact_contract.
    eapply list_drop_contract_contradiction.
    exact Heq.
  Qed.

  Lemma action_trace_tail_after_eval
        {from next finish : ChainState}
        act acts new_acts :
    reachable from ->
    from.(chain_state_queue) = act :: acts ->
    ActionEvaluation from act next new_acts ->
    next.(chain_state_queue) = new_acts ++ acts ->
    from.(chain_state_queue) <> finish.(chain_state_queue) ->
    ActionChainTrace from finish ->
    exists finish',
      inhabited (ActionChainTrace next finish') /\
      finish.(chain_state_queue) = finish'.(chain_state_queue).
  Proof.
    intros Hreach Hqueue Heval Hqueue_next Hneq trace.
    destruct (action_trace_step trace)
      as [Hsame | (mid & [Hstep] & [trace_tail])].
    - subst finish.
      exfalso.
      apply Hneq.
      reflexivity.
    - destruct Hstep as [act0 acts0 new_acts0 Hqueue_step Heval0 Hqueue_mid].
      rewrite Hqueue in Hqueue_step.
      inversion Hqueue_step; subst act0 acts0; clear Hqueue_step.
      pose proof
        (action_evaluation_deterministic
           from act next mid new_acts new_acts0
           Hreach Heval Heval0)
        as [Hnew_acts Henv].
      assert (Hqueue_mid_next :
          mid.(chain_state_queue) = next.(chain_state_queue)).
      { rewrite Hqueue_mid, Hqueue_next, Hnew_acts.
        reflexivity. }
      destruct
        (action_trace_external_equiv
           trace_tail
           ltac:(symmetry; exact Henv)
           Hqueue_mid_next)
        as (finish' & [trace_next_finish] & _ & Hqueue_finish).
      exists finish'.
      split.
      + constructor. auto.
      + exact Hqueue_finish.
  Qed.

  Lemma reachable_action_trace_to_list_drop st :
    reachable st ->
    exists finish_bstate,
      inhabited (ActionChainTrace st finish_bstate) /\
      finish_bstate.(chain_state_queue) =
        list_drop_contract_action st.(chain_state_queue).
  Proof.
    intros [trace].
    remember empty_state; induction trace as [|from mid to trace IH step]; subst.
    - exists empty_state.
      split.
      + constructor.
        apply clnil.
      + cbn.
        reflexivity.
    - specialize (IH ltac:(auto)).
      assert (Hreach_mid : reachable mid).
      { constructor.
        exact trace. }
      destruct step as
        [header Hqueue_prev Hvalid_header Hnext_accounts Horigin_eq Henv_eq
        |act acts new_acts finish_bstate Hqueue_prev Heval Hqueue_next
           Hact_account Htrace_finish Hqueue_finish
        |act acts new_acts Hqueue_prev Heval Hqueue_next Hact_contract
        |act acts fail_bstate act' acts' Henv_eq Hqueue_prev Hqueue_next
           Hact_account Htrace_fail Hqueue_fail Hno_eval].
      + exists to.
        split.
        * constructor.
          apply clnil.
        * rewrite no_drop_from_account by exact Hnext_accounts.
          reflexivity.
      + pose proof
          (reachable_queue_tail_accounts_from_account
             mid act acts Hreach_mid Hqueue_prev Hact_account)
          as Hacts_account.
        pose proof
          (eval_new_acts_from_contract_reachable
             mid act to new_acts Hreach_mid Heval)
          as Hnew_contract.
        assert (Hneq :
            mid.(chain_state_queue) <>
            finish_bstate.(chain_state_queue)).
        { intro Heq.
          rewrite Hqueue_prev, Hqueue_finish in Heq.
          apply (f_equal (@length Action)) in Heq.
          cbn in Heq.
          lia. }
        destruct
          (action_trace_tail_after_eval
             act acts new_acts Hreach_mid Hqueue_prev Heval Hqueue_next
             Hneq Htrace_finish)
          as (finish' & Htrace_next_finish & Hqueue_finish').
        exists finish'.
        split.
        * exact Htrace_next_finish.
        * rewrite <- Hqueue_finish'.
          rewrite Hqueue_finish.
          rewrite Hqueue_next.
          rewrite drop_from_contract by exact Hnew_contract.
          rewrite no_drop_from_account by exact Hacts_account.
          reflexivity.
      + destruct IH as (finish_bstate & [trace_finish] & Hqueue_finish).
        pose proof
          (eval_new_acts_from_contract_reachable
             mid act to new_acts Hreach_mid Heval)
          as Hnew_contract.
        assert (Hneq :
            mid.(chain_state_queue) <>
            finish_bstate.(chain_state_queue)).
        { intro Heq.
          rewrite Hqueue_finish in Heq.
          rewrite Hqueue_prev in Heq.
          eapply list_drop_contract_action_head_contract_neq;
            [exact Hact_contract | exact Heq]. }
        destruct
          (action_trace_tail_after_eval
             act acts new_acts Hreach_mid Hqueue_prev Heval Hqueue_next
             Hneq trace_finish)
          as (finish' & Htrace_next_finish & Hqueue_finish').
        exists finish'.
        split.
        * exact Htrace_next_finish.
        * rewrite <- Hqueue_finish'.
          rewrite Hqueue_finish.
          rewrite Hqueue_prev.
          rewrite list_drop_contract_action_cons_contract
            by exact Hact_contract.
          rewrite Hqueue_next.
          rewrite drop_from_contract by exact Hnew_contract.
          reflexivity.
      + pose proof
          (reachable_queue_tail_accounts_from_account
             mid act acts Hreach_mid Hqueue_prev Hact_account)
          as Hacts_account.
        exists to.
        split.
        * constructor.
          apply clnil.
        * rewrite Hqueue_next.
          rewrite no_drop_from_account by exact Hacts_account.
          reflexivity.
  Qed.

  Lemma act_from_contract_eval st act acts :
    reachable st ->
    st.(chain_state_queue) = act :: acts ->
    act_is_from_contract act ->
    exists new_env new_acts,
      inhabited (ActionEvaluation st act new_env new_acts).
  Proof.
    intros Hreach Hqueue Hfrom_contract.
    destruct (reachable_action_trace_to_list_drop st Hreach)
      as (finish_bstate & [trace_finish] & Hqueue_finish).
    destruct (action_trace_step trace_finish)
      as [Hsame | (next_bstate & [Hstep] & _)].
    - subst finish_bstate.
      rewrite Hqueue in Hqueue_finish.
      rewrite list_drop_contract_action_cons_contract in Hqueue_finish
        by exact Hfrom_contract.
      exfalso.
      eapply list_drop_contract_contradiction.
      exact Hqueue_finish.
    - destruct Hstep as [act0 acts0 new_acts Hqueue_step Heval Hqueue_next].
      rewrite Hqueue in Hqueue_step.
      inversion Hqueue_step; subst act0 acts0; clear Hqueue_step.
      exists next_bstate, new_acts.
      constructor.
      exact Heval.
  Qed.

  Lemma action_fail_false_contract_head_absurd
        (st : ChainState)
        (act : Action)
        (acts : list Action) :
    reachable st ->
    chain_state_queue st = act :: acts ->
    act_is_from_contract act ->
    exists (finish_bstate : ChainState),
      inhabited (ActionChainTrace st finish_bstate) /\
      finish_bstate.(chain_state_queue) = list_drop_contract_action acts.
  Proof.
    intros Hreach Hqueue Hfrom_contract.
    destruct (reachable_action_trace_to_list_drop st Hreach)
      as (finish_bstate & Htrace_finish & Hqueue_finish).
    exists finish_bstate.
    split.
    - exact Htrace_finish.
    - rewrite Hqueue in Hqueue_finish.
      rewrite list_drop_contract_action_cons_contract in Hqueue_finish
        by exact Hfrom_contract.
      exact Hqueue_finish.
  Qed.

  Lemma action_step_drop_le {from prev next : ChainState} :
    reachable_action_trace from prev ->
    ActionChainStep prev next ->
    length (list_drop_contract_action next.(chain_state_queue)) <=
    length (list_drop_contract_action prev.(chain_state_queue)).
  Proof.
    intros Hreach Hstep.
    destruct Hstep as [act acts new_acts Hqueue_prev Heval Hqueue_next].
    pose proof
      (emitted_acts_from_contract_in_action_trace
         Hreach Hqueue_prev Heval)
      as Hnew_contract.
    rewrite Hqueue_next, Hqueue_prev.
    rewrite drop_from_contract by exact Hnew_contract.
    unfold list_drop_contract_action at 2.
    cbn.
    destruct (address_is_contract (act_from act)); cbn.
    - unfold list_drop_contract_action. auto.
    - pose proof (list_drop_le
                    (fun act : Action => address_is_contract (act_from act))
                    acts).
      unfold list_drop_contract_action; lia.
  Qed.

  Lemma action_trace_drop_le {from st st' : ChainState} :
    reachable_action_trace from st ->
    ActionChainTrace st st' ->
    length (list_drop_contract_action st'.(chain_state_queue)) <=
    length (list_drop_contract_action st.(chain_state_queue)).
  Proof.
    intros Hreach trace.
    revert Hreach.
    induction trace as [|st mid st' trace IH step]; intros Hreach.
    - lia.
    - assert (Hreach_mid : reachable_action_trace from mid).
      { eapply reachable_action_trace_trans; eauto. }
      pose proof (action_step_drop_le Hreach_mid step) as Hstep.
      pose proof (IH Hreach) as Hprefix.
      lia.
  Qed.

  Lemma action_trace_finish_fail_absurd
        (st finish fail : ChainState)
        (act : Action)
        (acts : list Action)
        (act' : Action)
        (acts' : list Action) :
    reachable st ->
    st.(chain_state_queue) = act :: acts ->
    act_is_from_account act ->
    ActionChainTrace st finish ->
    finish.(chain_state_queue) = acts ->
    ActionChainTrace st fail ->
    fail.(chain_state_queue) = act' :: acts' ++ acts ->
    (forall new_env new_acts,
        ActionEvaluation fail act' new_env new_acts -> False) ->
    False.
  Proof.
    intros Hreach Hqueue Hact_account trace_finish Hqueue_finish
           trace_fail Hqueue_fail Hno_eval.
    pose proof
      (reachable_queue_tail_accounts_from_account
         st act acts Hreach Hqueue Hact_account)
      as Hacts_account.
    pose proof (reachable_action_trace_refl Hreach) as Hreach_at.
    destruct (action_trace_no_branch trace_finish trace_fail Hreach_at)
      as [(fail' & trace_finish_fail & Henv_fail & Hqueue_fail')
          | (finish' & trace_fail_finish & Henv_finish & Hqueue_finish')].
    - destruct (action_trace_step trace_finish_fail)
        as [Hsame | (next & [step_next] & [trace_next])].
      + subst fail'.
        rewrite Hqueue_finish in Hqueue_fail'.
        rewrite Hqueue_fail in Hqueue_fail'.
        apply (f_equal (@length Action)) in Hqueue_fail'. cbn in *.
        rewrite length_app in Hqueue_fail'.
        cbn in Hqueue_fail'.
        lia.
      + assert (Hreach_finish : reachable_action_trace st finish).
        { eapply reachable_action_trace_trans; eauto. }
        assert (Hreach_next : reachable_action_trace st next).
        { eapply reachable_action_trace_step; eauto. }
        destruct step_next as [act0 acts0 new_acts0 Hqueue_prev Heval Hqueue_next].
        rewrite Hqueue_finish in Hqueue_prev.
        destruct acts as [|a acts_tail].
        * discriminate.
        * inversion Hqueue_prev; subst act0 acts0; clear Hqueue_prev.
          inversion Hacts_account as [|? ? Ha_account Htail_account]; subst.
          pose proof
            (emitted_acts_from_contract_in_action_trace
               Hreach_finish Hqueue_finish Heval)
            as Hnew_contract.
          pose proof (action_trace_drop_le Hreach_next trace_next) as Hle.
          rewrite <- Hqueue_fail' in Hle.
          rewrite Hqueue_fail in Hle.
          rewrite Hqueue_next in Hle.
          rewrite drop_from_contract in Hle by exact Hnew_contract.
          assert (Hmono :
              length (list_drop_contract_action (a :: acts_tail)) <=
              length (list_drop_contract_action ((act' :: acts') ++ a :: acts_tail))).
          { apply list_drop_contract_app_le. }
          rewrite no_drop_from_account in Hmono.
          2: { constructor; assumption. }
          rewrite (no_drop_from_account acts_tail) in Hle by exact Htail_account.
          cbn -[list_drop_contract_action] in Hmono.
          lia.
    - destruct (action_trace_step trace_fail_finish)
        as [Hsame | (next & [step_next] & [trace_next])].
      + subst finish'.
        rewrite Hqueue_finish in Hqueue_finish'.
        rewrite Hqueue_fail in Hqueue_finish'.
        apply (f_equal (@length Action)) in Hqueue_finish'. cbn in *.
        rewrite length_app in Hqueue_finish'.
        cbn in Hqueue_finish'.
        lia.
      + destruct step_next as [act0 acts0 new_acts0 Hqueue_prev Heval Hqueue_next].
        rewrite Hqueue_fail in Hqueue_prev.
        inversion Hqueue_prev; subst act0 acts0; clear Hqueue_prev.
        eapply Hno_eval; eauto.
  Qed.

  Lemma chain_step_determin {prev1 prev2 next1 next2} :
    ChainStep prev1 next1 ->
    ChainStep prev2 next2 ->
    reachable prev1 ->
    reachable prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    prev1.(chain_state_queue) <> [] ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros Hstep1 Hstep2 Hreach1 Hreach2 Hequiv Hqueue_eq Hnonempty.
    destruct Hstep1 as
      [header1 Hq1 Hvalid1 Haccs1 Horigin1 Henv1
      | act1 acts1 new_acts1 finish1 Hq1 Heval1 Hq_next1
          Hfrom_acc1 Htrace_finish1 Hqueue_finish1
      | act1 acts1 new_acts1 Hq1 Heval1 Hq_next1 Hfrom_cont1
      | act1 acts1 fail1 act1' acts1' Henv1 Hq1 Hq_next1
          Hfrom_acc1 Htrace_fail1 Hqueue_fail1 Hno_eval1];
    destruct Hstep2 as
      [header2 Hq2 Hvalid2 Haccs2 Horigin2 Henv2
      | act2 acts2 new_acts2 finish2 Hq2 Heval2 Hq_next2
          Hfrom_acc2 Htrace_finish2 Hqueue_finish2
      | act2 acts2 new_acts2 Hq2 Heval2 Hq_next2 Hfrom_cont2
      | act2 acts2 fail2 act2' acts2' Henv2 Hq2 Hq_next2
          Hfrom_acc2 Htrace_fail2 Hqueue_fail2 Hno_eval2];
      try solve [exfalso; apply Hnonempty; exact Hq1];
      try solve [exfalso; apply Hnonempty; rewrite Hqueue_eq; exact Hq2].

    - (* user / user *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2; clear Hqueue_eq.
      assert (Hqueue12 : prev1.(chain_state_queue) = prev2.(chain_state_queue)).
      { rewrite Hq1, Hq2. now subst. }
      pose proof
        (action_evaluation_deterministic_strong
           Heval1 Heval2 Hreach1 Hreach2 Hequiv Hqueue12)
        as [Hnew_acts Henv_next].
      split; auto.
      rewrite Hq_next1, Hq_next2, Hnew_acts. now subst.

    - (* user / contract *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.

    - (* user / invalid *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2; clear Hqueue_eq.
      assert (Hqueue12 : prev1.(chain_state_queue) = prev2.(chain_state_queue)).
      { rewrite Hq1, Hq2. now subst. }
      destruct
        (action_trace_external_equiv
           Htrace_finish1 Hequiv Hqueue12)
        as (finish2' & [Htrace_finish2'] & Henv_finish & Hqueue_finish2').
      exfalso.
      eapply action_trace_finish_fail_absurd
        with (st := prev2)
             (finish := finish2')
             (fail := fail2)
             (act := act1)
             (acts := acts1)
             (act' := act2')
             (acts' := acts2'); eauto; try (rewrite_queue; now subst).

    - (* contract / user *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.

    - (* contract / contract *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2; clear Hqueue_eq.
      assert (Hqueue12 : prev1.(chain_state_queue) = prev2.(chain_state_queue)).
      { rewrite Hq1, Hq2. reflexivity. }
      pose proof
        (action_evaluation_deterministic_strong
           Heval1 Heval2 Hreach1 Hreach2 Hequiv Hqueue12)
        as [Hnew_acts Henv_next].
      split; auto.
      rewrite Hq_next1, Hq_next2, Hnew_acts.
      reflexivity.

    - (* contract / invalid *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.

    - (* invalid / user *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2; clear Hqueue_eq.
      assert (Hequiv_sym : EnvironmentEquiv prev2 prev1).
      { symmetry. exact Hequiv. }
      assert (Hqueue21 : prev2.(chain_state_queue) = prev1.(chain_state_queue)).
      { rewrite Hq1, Hq2. now subst. }
      destruct
        (action_trace_external_equiv
           Htrace_finish2 Hequiv_sym Hqueue21)
        as (finish1' & [Htrace_finish1'] & Henv_finish & Hqueue_finish1').
      exfalso.
      eapply action_trace_finish_fail_absurd
        with (st := prev1)
             (finish := finish1')
             (fail := fail1)
             (act := act1)
             (acts := acts1)
             (act' := act1')
             (acts' := acts1')
        ;try (rewrite_queue; now subst).

    - (* invalid / contract *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.

    - (* invalid / invalid *)
      rewrite Hq1 in Hqueue_eq.
      rewrite Hq2 in Hqueue_eq.
      inversion Hqueue_eq; subst act2 acts2; clear Hqueue_eq.
      split.
      + etransitivity; [exact Henv1|].
        etransitivity; [exact Hequiv|].
        symmetry; exact Henv2.
      + now subst.
  Qed.

  Lemma action_trace_finish_fail_absurd_general
        (st finish fail : ChainState)
        (target suffix : list Action)
        (act' : Action)
        (acts' : list Action) :
    reachable st ->
    Forall act_is_from_account target ->
    list_drop_contract_action suffix = target ->
    ActionChainTrace st finish ->
    finish.(chain_state_queue) = target ->
    ActionChainTrace st fail ->
    fail.(chain_state_queue) = act' :: acts' ++ suffix ->
    (forall new_env new_acts,
        ActionEvaluation fail act' new_env new_acts -> False) ->
    False.
  Proof.
    intros Hreach Htarget_account Hdrop_suffix trace_finish Hqueue_finish
           trace_fail Hqueue_fail Hno_eval.
    pose proof (reachable_action_trace_refl Hreach) as Hreach_at.
    destruct (action_trace_no_branch trace_finish trace_fail Hreach_at)
      as [(fail' & trace_finish_fail & Henv_fail & Hqueue_fail')
          | (finish' & trace_fail_finish & Henv_finish & Hqueue_finish')].
    - destruct (action_trace_step trace_finish_fail)
        as [Hsame | (next & [step_next] & [trace_next])].
      + subst fail'.
        assert (Htarget_len : length target <= length suffix).
        { rewrite <- Hdrop_suffix. apply list_drop_le. }
        rewrite Hqueue_finish in Hqueue_fail'.
        rewrite Hqueue_fail in Hqueue_fail'.
        apply (f_equal (@length Action)) in Hqueue_fail'.
        cbn in Hqueue_fail'. rewrite length_app in Hqueue_fail'.
        cbn in Hqueue_fail'.
        lia.
      + assert (Hreach_finish : reachable_action_trace st finish).
        { eapply reachable_action_trace_trans; eauto. }
        assert (Hreach_next : reachable_action_trace st next).
        { eapply reachable_action_trace_step; eauto. }
        destruct step_next as [act0 acts0 new_acts0 Hqueue_prev Heval Hqueue_next].
        rewrite Hqueue_finish in Hqueue_prev.
        destruct target as [|a target_tail].
        * discriminate.
        * inversion Hqueue_prev; subst act0 acts0; clear Hqueue_prev.
          inversion Htarget_account as [|? ? Ha_account Htail_account]; subst.
          pose proof
            (emitted_acts_from_contract_in_action_trace
               Hreach_finish Hqueue_finish Heval)
            as Hnew_contract.
          pose proof (action_trace_drop_le Hreach_next trace_next) as Hle.
          rewrite <- Hqueue_fail' in Hle.
          rewrite Hqueue_fail in Hle.
          rewrite Hqueue_next in Hle.
          apply Forall_cons_iff in Htarget_account as (? & ?).
          rewrite drop_from_contract in Hle by exact Hnew_contract.
          replace (act' :: acts' ++ suffix) with ((act' :: acts') ++ suffix) in Hle by auto.
          assert (Hmono :
              length (list_drop_contract_action suffix) <=
              length (list_drop_contract_action ((act' :: acts') ++ suffix)))
            by apply list_drop_app_le.
          rewrite Hdrop_suffix in *. cbn in Hmono, Hle.
          rewrite (no_drop_from_account target_tail) in Hle; auto.
          lia.
    - destruct (action_trace_step trace_fail_finish)
        as [Hsame | (next & [step_next] & [trace_next])].
      + subst finish'.
        assert (Htarget_len : length target <= length suffix).
        { rewrite <- Hdrop_suffix. apply list_drop_le. }
        rewrite Hqueue_finish in Hqueue_finish'.
        rewrite Hqueue_fail in Hqueue_finish'.
        apply (f_equal (@length Action)) in Hqueue_finish'.
        cbn in *; rewrite length_app in Hqueue_finish'.
        cbn in Hqueue_finish'.
        lia.
      + destruct step_next as [act0 acts0 new_acts0 Hqueue_prev Heval Hqueue_next].
        rewrite Hqueue_fail in Hqueue_prev.
        inversion Hqueue_prev; subst act0 acts0; clear Hqueue_prev.
        eapply Hno_eval; eauto.
  Qed.

End ChainStepDetermin.