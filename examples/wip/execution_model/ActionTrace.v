From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Psatz.
From Stdlib Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream ChainStream.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepDetermin.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepSerial.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.
From ConCert.Examples.Wip.ExecutionModel Require Import MyBuildUtils.
From stdpp Require countable.

Local Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
  end.

Section ClistLength.
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
    clist_length (clist_app xs ys) = clist_length xs + clist_length ys.
  Proof.
    induction ys; cbn.
    - lia.
    - replace (clist_length xs + S (clist_length ys)) with
        (S (clist_length xs + clist_length ys)) by lia.
      auto.
  Qed.
End ClistLength.

Section ActionTrace.
  Context {BaseTypes : ChainBase}.
  Context {Msg : Type} `{ser_msg : Serializable Msg}.

  Fixpoint incoming_calls_action_trace
            (Msg : Type) `{Serializable Msg}
            {from to : ChainState}
            (trace : ActionChainTrace from to)
            (caddr : Address) : option (list (ContractCallInfo Msg)) :=
    match trace with
    | snoc trace' step =>
      match step with
      | action_step _ _ _ _ _ _ (eval_call limit origin from to amount _ msg _ _ _ _ _ _ _ _ _ _ _ _) _ =>
        if (to =? caddr)%address then
          (* If there is a message it should deserialize correctly,
            otherwise the entire operation returns None. *)
          do hd_msg <- match msg with
                      | Some msg =>
                        match deserialize msg with
                        | Some msg => Some (Some msg)
                        | None => None
                        end
                      | None => Some None
                      end;
          do tl <- incoming_calls_action_trace Msg trace' caddr;
          Some (build_call_info limit origin from amount hd_msg :: tl)
        else
          incoming_calls_action_trace Msg trace' caddr
      | _ => incoming_calls_action_trace Msg trace' caddr
      end
    | _ => Some []
    end.

  Fixpoint action_trace_txs {from to : ChainState}
           (trace : ActionChainTrace from to) : list Tx :=
    match trace with
    | snoc trace' step =>
      match step with
      | action_step _ _ _ _ _ _ eval _ => eval_tx eval :: action_trace_txs trace'
      end
    | clnil => []
    end.

  Definition outgoing_txs_action_trace
             {from to : ChainState}
             (trace : ActionChainTrace from to)
             (caddr : Address) : list Tx :=
    filter (fun tx => (tx_from tx =? caddr)%address) (action_trace_txs trace).

  Lemma action_trace_txs_app {s1 s2 s3 : ChainState}
        (t1 : ActionChainTrace s1 s2) (t2 : ActionChainTrace s2 s3) :
    action_trace_txs (clist_app t1 t2) = action_trace_txs t2 ++ action_trace_txs t1.
  Proof.
    induction t2 as [|from mid to t2 IH step]; cbn; auto.
    destruct step. rewrite IH. reflexivity.
  Qed.

  Lemma outgoing_txs_action_trace_app {s1 s2 s3 : ChainState}
        (t1 : ActionChainTrace s1 s2) (t2 : ActionChainTrace s2 s3) caddr :
    outgoing_txs_action_trace (clist_app t1 t2) caddr =
    outgoing_txs_action_trace t2 caddr ++ outgoing_txs_action_trace t1 caddr.
  Proof.
    unfold outgoing_txs_action_trace. rewrite action_trace_txs_app, filter_app. reflexivity.
  Qed.

  Lemma eval_tx_equiv {pre1 pre2 post1 post2 : Environment} {act : Action} {na1 na2 : list Action}
        (e1 : ActionEvaluation pre1 act post1 na1)
        (e2 : ActionEvaluation pre2 act post2 na2) :
    EnvironmentEquiv pre1 pre2 ->
    (forall a wc, env_contracts pre1 a = Some wc -> address_is_contract a = true) ->
    eval_tx e1 = eval_tx e2.
  Proof.
    intros Henv Hfmt.
    destruct e1 as [l1 o1 f1 t1 a1 ? ? ? Hnc1 Hact1 ? ?
                   |l1 o1 f1 t1 a1 wc1 s1 st1 ? ? ? Hf1 Ht1 Hact1 ? ? ?
                   |l1 o1 f1 t1 a1 wc1 m1 ps1 ns1 ra1 ? ? ? Hd1 ? Hact1 ? ? ?];
    destruct e2 as [l2 o2 f2 t2 a2 ? ? ? Hnc2 Hact2 ? ?
                   |l2 o2 f2 t2 a2 wc2 s2 st2 ? ? ? Hf2 Ht2 Hact2 ? ? ?
                   |l2 o2 f2 t2 a2 wc2 m2 ps2 ns2 ra2 ? ? ? Hd2 ? Hact2 ? ? ?];
      cbn; rewrite Hact1 in Hact2; inversion Hact2; subst; auto;
      try (destruct m1; discriminate); try (destruct m2; discriminate).
    - (* transfer vs call None *)
      match goal with
      | H : act_transfer _ _ = match ?m with Some _ => _ | None => _ end |- _ =>
          destruct m; [discriminate|]; inversion H; subst
      end.
      rewrite <- Henv in Hd2. apply Hfmt in Hd2. congruence.
    -
      f_equal. apply countable.choose_proper.
      intros x. unfold fresh_address. rewrite Henv. reflexivity.
    - (* call None vs transfer *)
      match goal with
      | H : match ?m with Some _ => _ | None => _ end = act_transfer _ _ |- _ =>
          destruct m; [discriminate|]; inversion H; subst
      end.
      apply Hfmt in Hd1. congruence.
    - (* call vs call *)
      match goal with
      | H : match ?m1 with Some _ => _ | None => _ end = match ?m2 with Some _ => _ | None => _ end |- _ =>
          destruct m1, m2; inversion H; subst; reflexivity
      end.
  Qed.

  Local Lemma action_trace_chain_eq
        {from to : ChainState}
        (trace : ActionChainTrace from to) :
    (from : Chain) = (to : Chain).
  Proof.
    induction trace as [|from mid to trace IH step].
    - reflexivity.
    - transitivity (mid : Chain); [exact IH|].
      destruct step as [act acts new_acts Hqueue Heval Hqueue_next].
      destruct Heval; subst; rewrite_environment_equiv; cbn; reflexivity.
  Qed.

  Definition action_trace_length {st st'} : ActionChainTrace st st' -> nat
    := clist_length.

  Lemma trace_head_pattern_strong {from to} (trace : ActionChainTrace from to) :
    action_trace_length trace = 0 \/
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
        cbn in *. rewrite Htrace. auto.
  Qed.

  Fixpoint action_trace_nth {st st'}
      (n : nat) (trace : ActionChainTrace st st') : option ChainState :=
    match trace with
    | clnil =>
        match n with
        | 0 => Some st
        | S _ => None
        end
    | snoc trace' _ =>
        match n with
        | 0 => Some st'
        | S n' => action_trace_nth n' trace'
        end
    end.

  Local Lemma action_trace_nth_start
        {from to : ChainState}
        (trace : ActionChainTrace from to) :
    action_trace_nth (action_trace_length trace) trace = Some from.
  Proof.
    induction trace as [|from mid to trace IH step]; cbn; auto.
  Qed.

  Local Lemma action_trace_nth_finish
        {from to : ChainState}
        (trace : ActionChainTrace from to) :
    action_trace_nth 0 trace = Some to.
  Proof.
    destruct trace; reflexivity.
  Qed.

  Local Lemma reachable_step_local {from to : ChainState} :
    reachable from ->
    ChainStep from to ->
    reachable to.
  Proof.
    intros [trace] step.
    constructor.
    exact (snoc trace step).
  Qed.

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

  Local Lemma incoming_calls_action_trace_transport
        {origin1 origin2 from1 to1 from2 : ChainState}
        (trace1 : ActionChainTrace from1 to1)
        (caddr : Address) :
    reachable_action_trace origin1 from1 ->
    reachable_action_trace origin2 from2 ->
    EnvironmentEquiv from1 from2 ->
    from1.(chain_state_queue) = from2.(chain_state_queue) ->
    exists to2 (trace2 : ActionChainTrace from2 to2),
      EnvironmentEquiv to1 to2 /\
      to1.(chain_state_queue) = to2.(chain_state_queue) /\
      incoming_calls_action_trace Msg trace2 caddr =
        incoming_calls_action_trace Msg trace1 caddr /\
      action_trace_length trace2 = action_trace_length trace1 /\
      outgoing_txs_action_trace trace2 caddr = outgoing_txs_action_trace trace1 caddr.
  Proof.
    intros reach1 reach2 Henv Hqueue.
    generalize dependent from2.
    action_trace_induction; intros.
    - exists from2, clnil.
      repeat (split; auto).
    -
      destruct (IH ltac:(auto) from2 ltac:(auto) Henv Hqueue)
        as (mid2 & trace2 & Henv_mid & Hqueue_mid & Hinc_mid & Hlen_mid & Htxs_mid).
      assert (inhabited (ActionChainStep mid2 to)) as [Hstep2].
      {
        constructor.
        eapply action_step with (act := act) (acts := acts) (new_acts := new_acts); eauto.
        - now rewrite <- Hqueue_mid.
        - eapply action_evaluation_pre_equiv; eauto.
      }
      exists to, (snoc trace2 Hstep2).
      repeat (split; auto); cbn.
      + destruct_action_chain_step. rewrite_queue.
        inversion queue_prev. subst.
        apply list_app_eq_tl in queue_new; subst.
        do 2 destruct_action_eval; subst; cbn in *; rewrite Hinc_mid; auto;
        inversion act_eq; subst;
        try (destruct msg; try congruence);
        try (destruct msg0; try congruence);
        try congruence.
        * inversion H3. subst.
          destruct_address_eq; [subst|auto].
          assert (reach_mid : reachable_action_trace origin1 mid).
          { eapply reachable_action_trace_trans; eauto. }
          pose proof (contract_addr_format_in_action_trace caddr wc reach_mid ltac:(auto)) as ?.
          congruence.
        * inversion H3; subst.
          destruct_address_eq; [subst|auto].
          assert (reach_mid2 : reachable_action_trace origin2 mid2).
          { eapply reachable_action_trace_trans; eauto. }
          pose proof (contract_addr_format_in_action_trace caddr wc reach_mid2 ltac:(auto)) as ?.
          congruence.
        * inversion H3; subst.
          destruct_address_eq; [subst|]; auto.
        * inversion H3; subst.
          destruct_address_eq; [subst|]; auto.
      + auto.
      +
        assert (reach_mid : reachable_action_trace origin1 mid).
        { eapply reachable_action_trace_trans; eauto. }
        unfold outgoing_txs_action_trace in *.
        destruct Hstep2 as [act2 acts2 na2 Hq2 He2 Hq2'].
        cbn.
        rewrite Hqueue_mid in queue_prev. rewrite Hq2 in queue_prev.
        inversion queue_prev; subst act2 acts2.
        rewrite (eval_tx_equiv eval He2 Henv_mid).
        2: { intros a wc Hwc. eapply contract_addr_format_in_action_trace; eauto. }
        cbn [filter]. rewrite Htxs_mid. reflexivity.
  Qed.

  Local Lemma stream_action_step_chain_eq
        (str : ChainStream)
        (i : nat)
        {mid : ChainState}
        (step_model : ChainStep (CStr_nth i str) mid) :
    chain_state_queue (CStr_nth i str) <> [] ->
    EnvironmentEquiv mid (CStr_nth (S i) str) ->
    (CStr_nth i str : Chain) = (CStr_nth (S i) str : Chain).
  Proof.
    intros Hnonempty Henv_mid.
    destruct step_model as
      [header Hqueue_nil Hvalid Haccs Horig Henv_block
      |act acts new_acts finish Hqueue Heval Hqueue_next Hfrom_acc Htrace Hfinish
      |act acts new_acts Hqueue Heval Hqueue_next Hfrom_contract
      |act acts fail act' acts' Henv_invalid Hqueue Hqueue_next Hfrom_acc Htrace Hfail Hnoeval].
    - exfalso.
      apply Hnonempty.
      exact Hqueue_nil.
    - transitivity (mid : Chain).
      + destruct_action_eval; subst; cbn in *; setoid_rewrite env_eq; auto.
      + destruct Henv_mid; symmetry; auto.
    - transitivity (mid : Chain).
      + destruct_action_eval; subst; cbn in *; setoid_rewrite env_eq; auto.
      + destruct Henv_mid; symmetry; auto.
    - rewrite_environment_equiv. setoid_rewrite Henv_invalid. auto.
  Qed.

  Local Definition opt_list_app {A}
      (xs ys : option (list A)) : option (list A) :=
    match xs, ys with
    | Some xs, Some ys => Some (xs ++ ys)
    | _, _ => None
    end.

  Local Lemma opt_list_app_assoc {A}
        (xs ys zs : option (list A)) :
    opt_list_app xs (opt_list_app ys zs) =
    opt_list_app (opt_list_app xs ys) zs.
  Proof.
    destruct xs as [xs|], ys as [ys|], zs as [zs|];
      cbn; auto.
    now rewrite app_assoc.
  Qed.

  Local Lemma opt_list_app_some_r {A}
        (xs : option (list A)) (ys : list A) :
    opt_list_app xs (Some ys) =
      match xs with
      | Some xs => Some (xs ++ ys)
      | None => None
      end.
  Proof.
    destruct xs; reflexivity.
  Qed.

  Lemma incoming_calls_action_trace_app_option
        {caddr} {st1 st2 st3}
        (trace12 : ActionChainTrace st1 st2)
        (trace23 : ActionChainTrace st2 st3) :
    incoming_calls_action_trace Msg (clist_app trace12 trace23) caddr =
      opt_list_app
        (incoming_calls_action_trace Msg trace23 caddr)
        (incoming_calls_action_trace Msg trace12 caddr).
  Proof.
    induction trace23 as [|from mid to trace23 IH step].
    - cbn.
      destruct (incoming_calls_action_trace Msg trace12 caddr); reflexivity.
    - cbn.
      destruct step as [act acts new_acts Hqueue Heval Hqueue_new].
      rewrite IH.
      destruct_action_eval; cbn; try reflexivity.
      destruct (address_eqb to_addr caddr) eqn:Hto; cbn; try reflexivity.
      destruct msg as [msg_ser|]; cbn.
      + destruct (deserialize msg_ser); cbn;
          destruct (incoming_calls_action_trace Msg trace23 caddr); cbn;
          destruct (incoming_calls_action_trace Msg trace12 caddr); cbn; auto.
      + destruct (incoming_calls_action_trace Msg trace23 caddr); cbn;
          destruct (incoming_calls_action_trace Msg trace12 caddr); cbn; auto.
  Qed.

  Local Lemma action_trace_length_zero_finish
        {from to : ChainState}
        (trace : ActionChainTrace from to) :
    action_trace_length trace = 0 ->
    to = from.
  Proof.
    induction trace as [|from mid to trace IH step]; cbn; intro Hlen.
    - reflexivity.
    - lia.
  Qed.

  Local Lemma incoming_calls_action_trace_length_zero
        {from to : ChainState}
        (trace : ActionChainTrace from to)
        (caddr : Address) :
    action_trace_length trace = 0 ->
    incoming_calls_action_trace Msg trace caddr = Some [].
  Proof.
    induction trace as [|from mid to trace IH step]; cbn; intro Hlen.
    - reflexivity.
    - lia.
  Qed.

  Local Lemma outgoing_txs_action_trace_length_zero
        {from to : ChainState}
        (trace : ActionChainTrace from to)
        (caddr : Address) :
    action_trace_length trace = 0 ->
    outgoing_txs_action_trace trace caddr = [].
  Proof.
    induction trace as [|from mid to trace IH step]; cbn; intro Hlen.
    - reflexivity.
    - lia.
  Qed.

  Local Lemma opt_list_app_nil_l {A}
        (xs : option (list A)) :
    opt_list_app (Some []) xs = xs.
  Proof.
    destruct xs; reflexivity.
  Qed.

  Local Lemma action_trace_contract_prefix_cstr_correspond_opt
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        i prefix suffix finish
        (action_trace : ActionChainTrace (CStr_nth i str) finish)
        caddr base_inc :
    reachable (CStr_nth i str) ->
    Forall act_is_from_contract prefix ->
    Forall act_is_from_account suffix ->
    (CStr_nth i str).(chain_state_queue) = prefix ++ suffix ->
    finish.(chain_state_queue) = suffix ->
    incoming_calls Msg (CStr_clist str i) caddr = base_inc ->
    exists k,
      k = i + action_trace_length action_trace /\
      EnvironmentEquiv finish (CStr_nth k str) /\
      finish.(chain_state_queue) = (CStr_nth k str).(chain_state_queue) /\
      (CStr_nth i str : Chain) = (CStr_nth k str : Chain) /\
      incoming_calls Msg (CStr_clist str k) caddr =
        opt_list_app
          (incoming_calls_action_trace Msg action_trace caddr)
          base_inc /\
      outgoing_txs (CStr_clist str k) caddr =
        outgoing_txs_action_trace action_trace caddr ++ outgoing_txs (CStr_clist str i) caddr.
  Proof.
    intros Hreach Hprefix_contract Hsuffix_account Hqueue Hfinish_queue Hbase.
    remember (action_trace_length action_trace) as n eqn:Hlen.
    revert i prefix finish action_trace Hlen Hreach Hprefix_contract
           Hqueue Hfinish_queue Hbase.
    revert base_inc.
    induction n as [|n IH]; intros base_inc i prefix finish action_trace Hlen Hreach
      Hprefix_contract Hqueue Hfinish_queue Hbase.
    -
      assert (Hlen0 : action_trace_length action_trace = 0) by lia.

      pose proof
        (action_trace_length_zero_finish action_trace Hlen0)
        as Hfinish_eq.

      pose proof
        (incoming_calls_action_trace_length_zero
           action_trace caddr Hlen0)
        as Htrace_inc.

      subst finish.
      exists i.
      repeat split; try lia; try reflexivity.

      { rewrite Htrace_inc.
        rewrite opt_list_app_nil_l.
        exact Hbase. }
      rewrite (outgoing_txs_action_trace_length_zero action_trace caddr Hlen0).
      reflexivity.
    - destruct (trace_head_pattern_strong action_trace) as [Hzero | Hpat]; [lia|].
      destruct Hpat as (mid & step & trace_tail & Htrace_eq).
      destruct step as [act0 acts0 new_acts0 Hq0 Heval0 Hqmid].
      set (first_trace :=
        snoc clnil
          (@action_step BaseTypes (CStr_nth i str) mid act0 acts0 new_acts0
             Hq0 Heval0 Hqmid)) in *.
      change (clist_app first_trace trace_tail = action_trace) in Htrace_eq.
      subst action_trace.
      cbn in Hlen.
      destruct prefix as [|head prefix_tail].
      + destruct suffix as [|s suffix_tail].
        * pose proof Hq0 as Hq0_eq.
          rewrite Hqueue in Hq0_eq.
          cbn in Hq0_eq. discriminate.
        * cbn in Hqueue.
          pose proof Hq0 as Hq0_eq.
          rewrite Hqueue in Hq0_eq.
          inversion Hq0_eq; subst act0 acts0; clear Hq0_eq.
          pose proof
            (eval_new_acts_from_contract_reachable
               (CStr_nth i str) s mid new_acts0 Hreach Heval0)
            as Hnew_contract.
          assert (Hreach_mid : reachable_action_trace (CStr_nth i str) mid).
          { eapply reachable_action_trace_step; eauto.
            apply reachable_action_trace_refl; auto.
            eapply action_step; eauto. }
          pose proof (action_trace_drop_le Hreach_mid trace_tail) as Hdrop.
          rewrite Hqmid, Hfinish_queue in Hdrop.
          rewrite drop_from_contract in Hdrop by exact Hnew_contract.
          rewrite no_drop_from_account in Hdrop.
          2:{ inversion Hsuffix_account; subst; auto. }
          apply Forall_cons_iff in Hsuffix_account as (_ & Hsuffix_account).
          rewrite no_drop_from_account in Hdrop by exact Hsuffix_account.
          cbn in Hdrop. lia.
      + inversion Hprefix_contract as [|? ? Hhead_contract Hprefix_tail_contract]; subst.
        cbn in Hqueue.
        assert (Hq_first :
          (CStr_nth i str).(chain_state_queue) = head :: prefix_tail ++ chain_state_queue finish).
        { exact Hqueue. }
        pose proof Hq0 as Hq0_eq.
        rewrite Hqueue in Hq0_eq.
        inversion Hq0_eq; subst act0 acts0; clear Hq0_eq.
        assert (Hstep_contract : ChainStep (CStr_nth i str) mid).
        { eapply step_action_contract with
            (act := head) (acts := prefix_tail ++ chain_state_queue finish) (new_acts := new_acts0);
            eauto. }
        pose proof (CStr_link str i) as Hstream_step.
        assert (Hnonempty : chain_state_queue (CStr_nth i str) <> []).
        { rewrite Hq_first. cbn. discriminate. }
        destruct
          (chain_step_determin Hstep_contract Hstream_step
             Hreach (CStr_nth_reachable str start i)
             ltac:(reflexivity) ltac:(reflexivity) Hnonempty)
          as (Henv_mid & Hqueue_mid).
        assert (Hreach_mid : reachable_action_trace (CStr_nth i str) mid).
        { eapply reachable_action_trace_step; eauto.
          apply reachable_action_trace_refl; auto.
          eapply action_step; eauto. }
        destruct
          (@incoming_calls_action_trace_transport
             (CStr_nth i str) (CStr_nth (S i) str)
             mid finish (CStr_nth (S i) str)
             trace_tail caddr
             Hreach_mid
             (reachable_action_trace_refl
                (CStr_nth_reachable str start (S i)))
             Henv_mid Hqueue_mid)
          as (finish2 & trace_tail2 & Henv_finish2 & Hqueue_finish2
              & Hinc_trace_tail & Hlen_trace_tail2 & Htxs_trace_tail).
        pose proof
          (eval_new_acts_from_contract_reachable
             (CStr_nth i str) head mid new_acts0 Hreach Heval0)
          as Hnew_contract.
        assert (Hprefix_next :
          Forall act_is_from_contract (new_acts0 ++ prefix_tail)).
        { apply Forall_app; auto. }
        assert (Hqueue_next :
          (CStr_nth (S i) str).(chain_state_queue) =
            (new_acts0 ++ prefix_tail) ++ chain_state_queue finish).
        { rewrite <- Hqueue_mid. rewrite Hqmid. rewrite app_assoc. reflexivity. }
        assert (Hfinish2_queue : finish2.(chain_state_queue) = chain_state_queue finish).
        { rewrite <- Hqueue_finish2. auto. }
        assert (Hone :
          incoming_calls Msg (CStr_clist str (S i)) caddr =
          opt_list_app
            (incoming_calls_action_trace Msg first_trace caddr)
            (incoming_calls Msg (CStr_clist str i) caddr)).
        {
          subst first_trace.
          rewrite (cstr_clist_step_incoming_calls start Hstream_step).
          cbn.
          destruct_chain_step; destruct_action_eval; try destruct_action_eval;
            subst; rewrite_queue; auto; try congruence.
          all : try match goal with
            | H : _ :: _ = _ :: _ |- _ => inversion H; subst; clear H
            end.
          all : try match goal with
            | H : build_act _ _ _ _ = build_act _ _ _ _ |- _ => inversion H; subst; clear H
            | H : act_transfer _ _ = act_transfer _ _ |- _ => inversion H; subst; clear H
            | H : act_call _ _ _ = act_call _ _ _ |- _ => inversion H; subst; clear H
            | H : act_deploy _ _ _ = act_deploy _ _ _ |- _ => inversion H; subst; clear H
            | H : act_transfer _ _ = act_call _ _ _ |- _ => discriminate H
            | H : act_call _ _ _ = act_transfer _ _ |- _ => discriminate H
            | H : act_transfer _ _ = act_deploy _ _ _ |- _ => discriminate H
            | H : act_deploy _ _ _ = act_transfer _ _ |- _ => discriminate H
            | H : act_call _ _ _ = act_deploy _ _ _ |- _ => discriminate H
            | H : act_deploy _ _ _ = act_call _ _ _ |- _ => discriminate H
            | H : Some _ = Some _ |- _ => inversion H; subst; clear H
            end.
          all : try match goal with
            | H : act_transfer _ _ =
                    match ?msg with
                    | Some _ => act_call _ _ _
                    | None => act_transfer _ _
                    end |- _ =>
                destruct msg; cbn in H; [discriminate | inversion H; subst; clear H]
            | H : match ?msg with
                  | Some _ => act_call _ _ _
                  | None => act_transfer _ _
                  end = act_transfer _ _ |- _ =>
                destruct msg; cbn in H; [discriminate | inversion H; subst; clear H]
            | H : act_call _ _ _ =
                    match ?msg with
                    | Some _ => act_call _ _ _
                    | None => act_transfer _ _
                    end |- _ =>
                destruct msg; cbn in H; [inversion H; subst; clear H | discriminate]
            | H : match ?msg with
                  | Some _ => act_call _ _ _
                  | None => act_transfer _ _
                  end = act_call _ _ _ |- _ =>
                destruct msg; cbn in H; [inversion H; subst; clear H | discriminate]
            end.
          all : try match goal with
            | Hc : env_contracts _ ?addr = Some ?wc,
              Hn : address_is_contract ?addr = false |- _ =>
                pose proof (contract_addr_format addr wc Hreach Hc);
                congruence
            | Hn : address_is_contract ?addr = false,
              Hc : env_contracts _ ?addr = Some ?wc |- _ =>
                pose proof (contract_addr_format addr wc Hreach Hc);
                congruence
            end.
          all : cbn.
          all : try (destruct (incoming_calls Msg (CStr_clist str i) caddr); reflexivity).
          all : destruct msg as [msg_ser|]; try destruct msg0 as [msg_ser0|];
            inversion H3; subst.
          all : destruct (address_eqb_spec to_addr caddr) as [->|];
            try (destruct (incoming_calls Msg (CStr_clist str i) caddr); reflexivity).
          all : destruct (deserialize msg_ser); cbn; auto.
        }

        assert (Hone_txs :
          outgoing_txs (CStr_clist str (S i)) caddr =
          outgoing_txs_action_trace first_trace caddr ++ outgoing_txs (CStr_clist str i) caddr).
        {
          subst first_trace.
          rewrite CStr_clist_snoc.
          unfold outgoing_txs, outgoing_txs_action_trace.
          destruct (CStr_link str i) as
            [hd Hqn Hv1 Hv2 Hv3 Hv4
            |act_l acts_l na_l fin_l Hql eval_l Hqn_l Hfrom_l Htr_l Hqf_l
            |act_l acts_l na_l Hql eval_l Hqn_l Hfrom_l
            |act_l acts_l fail_l act_l' acts_l' Henv_l Hql Hqn_l Hfrom_l Htr_l Hqf_l Hne_l];
            cbn [trace_txs action_trace_txs].
          - rewrite Hq_first in Hqn. discriminate.
          - rewrite Hq_first in Hql. inversion Hql; subst act_l acts_l.
            unfold act_is_from_account, act_is_from_contract in *. congruence.
          - rewrite Hq_first in Hql. inversion Hql; subst act_l acts_l.
            cbn [trace_txs action_trace_txs].
            rewrite (eval_tx_equiv eval_l Heval0 ltac:(reflexivity)).
            2: { intros a wc Hwc. eapply contract_addr_format; eauto. }
            cbn [filter]. destruct (_ =? _)%address; reflexivity.
          - rewrite Hq_first in Hql. inversion Hql; subst act_l acts_l.
            unfold act_is_from_account, act_is_from_contract in *. congruence.
        }
        assert (n = action_trace_length trace_tail).
        { unfold action_trace_length in *.
          rewrite clist_length_app in Hlen; auto.
        }

        destruct
          (IH (incoming_calls Msg (CStr_clist str (S i)) caddr)
             (S i) (new_acts0 ++ prefix_tail) finish2 trace_tail2
             ltac:(rewrite Hlen_trace_tail2; cbn in Hlen; lia)
             (CStr_nth_reachable str start (S i))
             Hprefix_next Hqueue_next Hfinish2_queue ltac:(reflexivity))
          as (k & Hk_eq & Henv_fin & Hqueue_fin & Hchain_tail & Hinc_k & Htxs_k).
        exists k.
        split; [|split; [|repeat split]].
        * rewrite Hk_eq. cbn. lia.
        * etransitivity; [exact Henv_finish2|exact Henv_fin].
        * rewrite Hqueue_finish2. exact Hqueue_fin.
        * transitivity (CStr_nth (S i) str : Chain).
          -- eapply stream_action_step_chain_eq; eauto. reflexivity.
          -- exact Hchain_tail.
        * rewrite Hinc_trace_tail in Hinc_k.
          rewrite Hone in Hinc_k.
          rewrite opt_list_app_assoc in Hinc_k.
          rewrite <- (incoming_calls_action_trace_app_option
                       (caddr := caddr) first_trace trace_tail) in Hinc_k.
          subst first_trace.
          exact Hinc_k.
        * rewrite Htxs_k, Htxs_trace_tail, Hone_txs.
          rewrite outgoing_txs_action_trace_app, app_assoc.
          reflexivity.
  Qed.

  Local Lemma action_trace_contract_prefix_cstr_correspond
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        i prefix suffix finish
        (action_trace : ActionChainTrace (CStr_nth i str) finish)
        caddr inc_calls :
    reachable (CStr_nth i str) ->
    Forall act_is_from_contract prefix ->
    Forall act_is_from_account suffix ->
    (CStr_nth i str).(chain_state_queue) = prefix ++ suffix ->
    finish.(chain_state_queue) = suffix ->
    incoming_calls Msg (CStr_clist str i) caddr = Some inc_calls ->
    exists k,
      k = i + action_trace_length action_trace /\
      EnvironmentEquiv finish (CStr_nth k str) /\
      finish.(chain_state_queue) = (CStr_nth k str).(chain_state_queue) /\
      (CStr_nth i str : Chain) = (CStr_nth k str : Chain) /\
      incoming_calls Msg (CStr_clist str k) caddr =
        match incoming_calls_action_trace Msg action_trace caddr with
        | Some finish_inc_calls => Some (finish_inc_calls ++ inc_calls)
        | None => None
        end.
  Proof.
    intros Hreach Hprefix_contract Hsuffix_account Hqueue Hfinish_queue Hinc.
    destruct
      (action_trace_contract_prefix_cstr_correspond_opt
         str start i prefix suffix finish action_trace caddr (Some inc_calls)
         Hreach Hprefix_contract Hsuffix_account Hqueue Hfinish_queue Hinc)
      as (k & Hk & Henv & Hqueue_k & Hchain & Hinc_k & _).
    exists k.
    split; [|split; [|repeat split]]; auto.
  Qed.

  Lemma action_trace_cstr_nth_correspond_general
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        i act acts finish
        (action_trace : ActionChainTrace (CStr_nth i str) finish)
        caddr inc_calls :
    reachable (CStr_nth i str) ->
    (CStr_nth i str).(chain_state_queue) = act :: acts ->
    act_is_from_account act ->
    finish.(chain_state_queue) = acts ->
    incoming_calls Msg (CStr_clist str i) caddr = Some inc_calls ->
    exists k,
      k = i + action_trace_length action_trace /\
      EnvironmentEquiv finish (CStr_nth k str) /\
      finish.(chain_state_queue) = (CStr_nth k str).(chain_state_queue) /\
      (CStr_nth i str : Chain) = (CStr_nth k str : Chain) /\
      incoming_calls Msg (CStr_clist str k) caddr =
        match incoming_calls_action_trace Msg action_trace caddr with
        | Some finish_inc_calls => Some (finish_inc_calls ++ inc_calls)
        | None => None
        end /\
      outgoing_txs (CStr_clist str k) caddr =
        outgoing_txs_action_trace action_trace caddr ++ outgoing_txs (CStr_clist str i) caddr.
  Proof.
    intros Hreach Hqueue Hfrom_account Hfinish_queue Hinc.
    destruct (trace_head_pattern_strong action_trace) as [Hzero | Hpat].
    - (* n = 0 *)
      assert (Hlen0 : action_trace_length action_trace = 0) by lia.
      pose proof
        (action_trace_length_zero_finish action_trace Hlen0)
        as Hfinish_eq.
      pose proof
        (incoming_calls_action_trace_length_zero
           action_trace caddr Hlen0)
        as Htrace_inc.
      subst finish.
      exists i.
      repeat split; try lia; try reflexivity.
      { rewrite Htrace_inc. auto. }
      rewrite (outgoing_txs_action_trace_length_zero action_trace caddr Hlen0).
      reflexivity.
    - destruct Hpat as (mid & step & trace_tail & Htrace_eq).
      pose (snoc clnil step ++ trace_tail)%trace as action_trace_finish.
      destruct step as [act0 acts0 new_acts0 Hq0 Heval0 Hqmid].
      rewrite_queue. inversion Hqueue; subst act acts acts0.
      assert (Hstep_user : ChainStep (CStr_nth i str) mid).
      { eapply step_action_user with (finish_bstate := finish); eauto. }
      assert (inhabited (ActionChainTrace (CStr_nth i str) finish)) as action_trace_finish_inhabited.
      { constructor; auto. }
      clear action_trace_finish.
      set (first_trace :=
        snoc clnil
          (@action_step BaseTypes (CStr_nth i str) mid act0 finish.(chain_state_queue)
            new_acts0 Hq0 Heval0 Hqmid)) in *.
      change (clist_app first_trace trace_tail = action_trace) in Htrace_eq.
      subst action_trace.
      pose proof Hq0 as Hq0_eq.
      pose proof (CStr_link str i) as Hstream_step.
      assert (Hnonempty : chain_state_queue (CStr_nth i str) <> []).
      { rewrite_queue. discriminate. }
      destruct
        (chain_step_determin Hstep_user Hstream_step
           Hreach (CStr_nth_reachable str start i)
           ltac:(reflexivity) ltac:(reflexivity) Hnonempty)
        as (Henv_mid & Hqueue_mid).
      assert (Hreach_mid : reachable_action_trace (CStr_nth i str) mid).
      { eapply reachable_action_trace_step; eauto.
        apply reachable_action_trace_refl. exact Hreach.
        eapply action_step; eauto. }
      destruct
        (@incoming_calls_action_trace_transport
           (CStr_nth i str) (CStr_nth (S i) str)
           mid finish (CStr_nth (S i) str)
           trace_tail caddr
           Hreach_mid
           (reachable_action_trace_refl
              (CStr_nth_reachable str start (S i)))
           Henv_mid Hqueue_mid)
        as (finish2 & trace_tail2 & Henv_finish2 & Hqueue_finish2
            & Hinc_trace_tail & Hlen_tail2 & Htxs_trace_tail).
      pose proof
        (eval_new_acts_from_contract_reachable
           (CStr_nth i str) act0 mid new_acts0 Hreach Heval0)
        as Hnew_contract.
      pose proof
        (reachable_queue_tail_accounts_from_account
           (CStr_nth i str) act0 finish.(chain_state_queue) Hreach ltac:(auto) Hfrom_account)
        as Hacts_account.
      assert (Hinc_next :
        incoming_calls Msg (CStr_clist str (S i)) caddr =
        opt_list_app
          (incoming_calls_action_trace Msg first_trace caddr)
          (Some inc_calls)).
      {
        rewrite (cstr_clist_step_incoming_calls start Hstream_step).
        subst first_trace.
        cbn.
        rewrite Hinc.
        destruct Hstream_step; destruct_action_eval; try destruct_action_eval;
          subst; rewrite_queue; auto; try congruence.
        all : inversion Hq0; subst.
        all : try destruct msg as [msg_ser|] eqn:Hmsg; try inversion H3; subst.
        all : try match goal with
          | H : _ :: _ = _ :: _ |- _ => inversion H; subst; clear H
          end.
        all : try match goal with
          | H : build_act _ _ _ _ = build_act _ _ _ _ |- _ => inversion H; subst; clear H
          | H : act_transfer _ _ = act_transfer _ _ |- _ => inversion H; subst; clear H
          | H : act_call _ _ _ = act_call _ _ _ |- _ => inversion H; subst; clear H
          | H : act_deploy _ _ _ = act_deploy _ _ _ |- _ => inversion H; subst; clear H
          | H : act_transfer _ _ = act_call _ _ _ |- _ => discriminate H
          | H : act_call _ _ _ = act_transfer _ _ |- _ => discriminate H
          | H : act_transfer _ _ = act_deploy _ _ _ |- _ => discriminate H
          | H : act_deploy _ _ _ = act_transfer _ _ |- _ => discriminate H
          | H : act_call _ _ _ = act_deploy _ _ _ |- _ => discriminate H
          | H : act_deploy _ _ _ = act_call _ _ _ |- _ => discriminate H
          | H : Some _ = Some _ |- _ => inversion H; subst; clear H
          end.
        all : try match goal with
          | H : act_transfer _ _ =
                  match ?msg with
                  | Some _ => act_call _ _ _
                  | None => act_transfer _ _
                  end |- _ =>
              destruct msg; cbn in H; [discriminate | inversion H; subst; clear H]
          | H : match ?msg with
                | Some _ => act_call _ _ _
                | None => act_transfer _ _
                end = act_transfer _ _ |- _ =>
              destruct msg; cbn in H; [discriminate | inversion H; subst; clear H]
          | H : act_call _ _ _ =
                  match ?msg with
                  | Some _ => act_call _ _ _
                  | None => act_transfer _ _
                  end |- _ =>
              destruct msg; cbn in H; [inversion H; subst; clear H | discriminate]
          | H : match ?msg with
                | Some _ => act_call _ _ _
                | None => act_transfer _ _
                end = act_call _ _ _ |- _ =>
              destruct msg; cbn in H; [inversion H; subst; clear H | discriminate]
          end.
        all : try match goal with
          | Hc : env_contracts _ ?addr = Some ?wc,
            Hn : address_is_contract ?addr = false |- _ =>
              pose proof (contract_addr_format addr wc Hreach Hc);
              congruence
          | Hn : address_is_contract ?addr = false,
            Hc : env_contracts _ ?addr = Some ?wc |- _ =>
              pose proof (contract_addr_format addr wc Hreach Hc);
              congruence
          end.
        all : cbn; try (destruct (incoming_calls Msg (CStr_clist str i) caddr); reflexivity).
        all : try destruct (address_eqb_spec to_addr0 caddr) as [->|]; auto.
        all : try destruct (address_eqb_spec to_addr caddr) as [->|]; auto.
        all : try destruct (deserialize s) eqn:Hs_deser; cbn; auto.
        (* all : try destruct (deserialize msg_ser) eqn:Hmsg_deser; cbn; auto. *)
        - (* action_invalid *)
          exfalso. destruct action_trace_finish_inhabited as [action_trace].
          eapply action_trace_finish_fail_absurd_general with
            (finish := finish) (fail := fail_bstate); eauto.
          rewrite drop_from_contract; auto.
          rewrite no_drop_from_account; auto.
        - (* action_invalid *)
          exfalso. destruct action_trace_finish_inhabited as [action_trace].
          eapply action_trace_finish_fail_absurd_general with
            (finish := finish) (fail := fail_bstate); eauto.
          rewrite drop_from_contract; auto.
          rewrite no_drop_from_account; auto.
      }

      assert (Hone_txs :
        outgoing_txs (CStr_clist str (S i)) caddr =
        outgoing_txs_action_trace first_trace caddr ++ outgoing_txs (CStr_clist str i) caddr).
      {
        subst first_trace.
        rewrite CStr_clist_snoc.
        unfold outgoing_txs, outgoing_txs_action_trace.
        destruct (CStr_link str i) as
          [hd Hqn Hv1 Hv2 Hv3 Hv4
          |act_l acts_l na_l fin_l Hql eval_l Hqn_l Hfrom_l Htr_l Hqf_l
          |act_l acts_l na_l Hql eval_l Hqn_l Hfrom_l
          |act_l acts_l fail_l act_l' acts_l' Henv_l Hql Hqn_l Hfrom_l Htr_l Hqf_l Hne_l];
          cbn [trace_txs action_trace_txs].
        - rewrite Hq0 in Hqn. discriminate.
        - rewrite Hq0 in Hql. inversion Hql; subst act_l acts_l.
          rewrite (eval_tx_equiv eval_l Heval0 ltac:(reflexivity)).
          2: { intros a wc Hwc. eapply contract_addr_format; eauto. }
          cbn [filter]. destruct (_ =? _)%address; reflexivity.
        - rewrite Hq0 in Hql. inversion Hql; subst act_l acts_l.
          unfold act_is_from_account, act_is_from_contract in *. congruence.
        -
          rewrite Hq0 in Hql. inversion Hql; subst act_l acts_l.
          exfalso. destruct action_trace_finish_inhabited as [action_trace].
          eapply action_trace_finish_fail_absurd_general with
            (finish := finish) (fail := fail_l); eauto.
          match goal with
          | H : chain_state_queue finish = chain_state_queue (CStr_nth (S i) str) |- _ => rewrite <- H
          end.
          rewrite no_drop_from_account; auto.
      }
      destruct
        (action_trace_contract_prefix_cstr_correspond_opt
           str start (S i) new_acts0 finish.(chain_state_queue) finish2 trace_tail2 caddr
           (incoming_calls Msg (CStr_clist str (S i)) caddr))
        as (k & Hk_eq & Henv_tail & Hqueue_tail & Hchain_tail & Hinc_k & Htxs_k); auto.
      + apply CStr_nth_reachable. exact start.
      + rewrite <- Hqueue_mid. rewrite Hqmid. reflexivity.
      + exists k.
        split; [|split; [|repeat split]].
        * rewrite Hk_eq. cbn. subst first_trace. cbn.
          unfold action_trace_length in *. rewrite clist_length_app.
          cbn. rewrite Hlen_tail2. lia.
        * etransitivity; [exact Henv_finish2|exact Henv_tail].
        * rewrite Hqueue_finish2. exact Hqueue_tail.
        * transitivity (CStr_nth (S i) str : Chain); auto.
          eapply stream_action_step_chain_eq; eauto. reflexivity.
        * rewrite Hinc_trace_tail in Hinc_k.
          rewrite Hinc_next in Hinc_k.
          rewrite opt_list_app_assoc in Hinc_k.
          rewrite <- (incoming_calls_action_trace_app_option
                       (caddr := caddr) first_trace trace_tail) in Hinc_k.
          rewrite opt_list_app_some_r in Hinc_k.
          exact Hinc_k.
        * rewrite Htxs_k, Htxs_trace_tail, Hone_txs.
          rewrite outgoing_txs_action_trace_app, app_assoc.
          reflexivity.
  Qed.

  Lemma action_trace_cstr_nth_correspond
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        i act acts finish
        (action_trace : ActionChainTrace (CStr_nth i str) finish)
        caddr inc_calls :
    reachable (CStr_nth i str) ->
    (CStr_nth i str).(chain_state_queue) = act :: acts ->
    act_is_from_account act ->
    finish.(chain_state_queue) = acts ->
    incoming_calls Msg (CStr_clist str i) caddr = Some inc_calls ->
    exists k,
      (i <= k)%nat /\
      EnvironmentEquiv finish (CStr_nth k str) /\
      finish.(chain_state_queue) = (CStr_nth k str).(chain_state_queue) /\
      (CStr_nth i str : Chain) = (CStr_nth k str : Chain) /\
      incoming_calls Msg (CStr_clist str k) caddr =
        match incoming_calls_action_trace Msg action_trace caddr with
        | Some finish_inc_calls => Some (finish_inc_calls ++ inc_calls)
        | None => None
        end /\
      outgoing_txs (CStr_clist str k) caddr =
        outgoing_txs_action_trace action_trace caddr ++ outgoing_txs (CStr_clist str i) caddr.
  Proof.
    intros Hreach Hqueue Hfrom_account Hfinish_queue Hinc.
    destruct
      (action_trace_cstr_nth_correspond_general
         str start i act acts finish action_trace caddr inc_calls
         Hreach Hqueue Hfrom_account Hfinish_queue Hinc)
      as (k & Hk & Henv & Hqueue_k & Hchain & Hinc_k & Htxs_k).
    exists k.
    split; [|split; [|repeat split]]; try lia; auto.
  Qed.

End ActionTrace.
