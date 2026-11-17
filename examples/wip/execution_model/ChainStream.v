From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Lia.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import MyBuildUtils.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.

From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepDetermin.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepSerial.

Section ChainStream.
  Context {BaseTypes : ChainBase}.

  Definition ChainStream := @ChainedStream ChainState ChainStep.

  Lemma CStr_nth_reachable
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state) :
      forall i, reachable (CStr_nth i str).
  Proof.
    intro i.
    unfold reachable.
    rewrite <- start.
    constructor.
    exact (CStr_clist str i).
  Qed.

  Lemma CStr_wc_preserve {wc}
            {i : nat}
            {caddr} (str : ChainStream) :
    env_contracts (CStr_nth i str) caddr = Some wc ->
    forall j,
      (i <= j)%nat ->
      env_contracts (CStr_nth j str) caddr = Some wc.
  Proof.
    intros deployed * Hij.
    pose (CStr_clist_n_m str i j Hij) as trace.
    eapply (wc_preserve); eauto.
  Qed.

  Lemma CStr_deploy_info_eq {Setup : Type} `{ser_setup : Serializable Setup}
      (str : ChainStream) (start : CStr_nth 0 str = empty_state) i caddr :
    deployment_info Setup (CStr_clist_start str start i) caddr
      = deployment_info Setup (CStr_clist str i) caddr.
  Proof.
    destruct start; auto.
  Qed.

  Lemma CStr_incoming_calls_eq {Msg : Type} `{ser_msg   : Serializable Msg}
      (str : ChainStream) (start : CStr_nth 0 str = empty_state) i caddr :
    incoming_calls Msg (CStr_clist_start str start i) caddr
      = incoming_calls Msg (CStr_clist str i) caddr.
  Proof.
    destruct start; auto.
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

  Local Lemma action_eval_limit_positive
        {st act next_st new_acts} :
    ActionEvaluation st act next_st new_acts ->
    (0 < act_limit act)%nat.
  Proof.
    intro Heval.
    destruct Heval; subst; cbn; lia.
  Qed.

  Local Lemma action_eval_new_acts_limit_le
        n {st act next_st new_acts} :
    ActionEvaluation st act next_st new_acts ->
    (act_limit act <= S n)%nat ->
    Forall (fun act' => (act_limit act' <= n)%nat) new_acts.
  Proof.
    intros Heval Hlimit.
    destruct Heval; subst; cbn in *; try constructor.
    apply Forall_forall.
    intros act' Hact'.
    apply in_map_iff in Hact'.
    destruct Hact' as (body & <- & _).
    cbn.
    lia.
  Qed.

  Local Lemma cstr_action_prefix_terminate
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state) :
    forall n acts1 i acts2,
      Forall (fun act => (act_limit act <= n)%nat) acts1 ->
      (CStr_nth i str).(chain_state_queue) = acts1 ++ acts2 ->
      exists j,
        (i <= j)%nat /\
        (CStr_nth j str).(chain_state_queue) = acts2.
  Proof.
    induction n as [|n IHn].
    - induction acts1 as [|act acts1 IHacts1];
        intros i acts2 Hlimits Hqueue.
      + exists i.
        split; [lia|].
        cbn in Hqueue.
        exact Hqueue.
      + inversion Hlimits as [|? ? Hlimit_act Hlimits_tail]; subst.
        pose proof (CStr_link str i) as Hstep.
        destruct_chain_step.
        * rewrite_queue.
          discriminate.
        * pose proof (action_eval_limit_positive eval) as Hpositive.
          rewrite Hqueue in queue_prev.
          cbn in queue_prev.
          inversion queue_prev; subst act acts; clear queue_prev.
          cbn in Hlimit_act.
          lia.
        * pose proof (action_eval_limit_positive eval) as Hpositive.
          rewrite Hqueue in queue_prev.
          cbn in queue_prev.
          inversion queue_prev; subst act acts; clear queue_prev.
          cbn in Hlimit_act.
          lia.
        * rewrite_queue. cbn in *.
          inversion Hqueue; subst act0 acts; clear queue_prev.
          destruct (IHacts1 (S i) acts2 Hlimits_tail )
            as (j & Hij & Hqueue_j); auto.
          exists j.
          split; [lia|exact Hqueue_j].
    - induction acts1 as [|act acts1 IHacts1];
        intros i acts2 Hlimits Hqueue.
      + exists i.
        split; [lia|].
        cbn in Hqueue.
        exact Hqueue.
      + inversion Hlimits as [|? ? Hlimit_act Hlimits_tail]; subst.
        pose proof (CStr_link str i) as Hstep.
        destruct_chain_step.
        * rewrite Hqueue in queue_prev.
          discriminate.
        * rewrite Hqueue in queue_prev.
          cbn in queue_prev.
          inversion queue_prev; subst act acts; clear queue_prev.
          pose proof
            (action_eval_new_acts_limit_le n eval Hlimit_act)
            as Hnew_limits.
          rewrite <- H1 in *.
          destruct
            (IHn new_acts (S i) (acts1 ++ acts2)
               Hnew_limits queue_new)
            as (k & Hik & Hqueue_k).
          destruct (IHacts1 k acts2 Hlimits_tail Hqueue_k)
            as (j & Hkj & Hqueue_j).
          exists j.
          split; [lia|exact Hqueue_j].
        * rewrite Hqueue in queue_prev.
          cbn in queue_prev.
          inversion queue_prev; subst; clear queue_prev.
          pose proof
            (action_eval_new_acts_limit_le n eval Hlimit_act)
            as Hnew_limits.
          destruct
            (IHn new_acts (S i) (acts1 ++ acts2)
               Hnew_limits queue_new)
            as (k & Hik & Hqueue_k).
          destruct (IHacts1 k acts2 Hlimits_tail Hqueue_k)
            as (j & Hkj & Hqueue_j).
          exists j.
          split; [lia|exact Hqueue_j].
        * rewrite Hqueue in queue_prev.
          cbn in queue_prev.
          inversion queue_prev; subst; clear queue_prev.
          destruct (IHacts1 (S i) acts2 Hlimits_tail)
            as (j & Hij & Hqueue_j); auto.
          exists j.
          split; [lia|exact Hqueue_j].
  Qed.

  Lemma cstr_act_terminate
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        i act acts :
    (CStr_nth i str).(chain_state_queue) = act :: acts ->
    exists j,
      (i <= j)%nat /\
      (CStr_nth j str).(chain_state_queue) = acts.
  Proof.
    intro Hqueue.
    change (act :: acts) with ([act] ++ acts) in Hqueue.
    eapply cstr_action_prefix_terminate with
      (n := act_limit act)
      (acts1 := [act]); eauto.
  Qed.

  Lemma cstr_act_hd_finally (str : ChainStream) (start : CStr_nth 0 str = empty_state)
      i act :
    List.In act (CStr_nth i str).(chain_state_queue) ->
    exists j,
      (i <= j)%nat /\
      List.hd_error (CStr_nth j str).(chain_state_queue) = Some act.
  Proof.
    intro Hact_in_queue.
    apply List.in_split in Hact_in_queue
      as (before & after & Hqueue).
    revert i Hqueue.
    induction before as [|head before IH]; intros i Hqueue.
    - exists i.
      split; [lia|].
      cbn in Hqueue.
      rewrite Hqueue.
      reflexivity.
    - cbn in Hqueue.
      destruct
        (cstr_act_terminate
           str start i head (before ++ act :: after) Hqueue)
        as (k & Hik & Hqueue_k).
      destruct (IH k Hqueue_k)
        as (j & Hkj & Hhd_j).
      exists j.
      split; [lia|exact Hhd_j].
  Qed.

  Local Lemma deployment_info_env_contracts_some
        {Setup : Type} `{ser_setup : Serializable Setup}
        {from to : ChainState}
        (trace : ChainTrace from to)
        caddr dep_info :
    deployment_info Setup trace caddr = Some dep_info ->
    env_contracts to caddr <> None.
  Proof.
    intro Hdep.
    induction trace as [|from mid to trace IH step].
    - cbn in Hdep. discriminate.
    - cbn in Hdep.
      destruct_chain_step.
      + rewrite_environment_equiv. eauto.
      + destruct eval; rewrite_environment_equiv; cbn in *; eauto.
        rewrite (address_eq_sym caddr) in *.
        destruct_address_eq; try discriminate; eauto.
      + destruct eval; rewrite_environment_equiv; cbn in *; eauto.
        rewrite (address_eq_sym caddr) in *.
        destruct_address_eq; try discriminate; eauto.
      + rewrite_environment_equiv. eauto.
  Qed.

  Local Lemma deployment_info_snoc_preserve
        {Setup : Type} `{ser_setup : Serializable Setup}
        {from mid to : ChainState}
        (trace : ChainTrace from mid)
        (step : ChainStep mid to)
        caddr dep_info :
    deployment_info Setup trace caddr = Some dep_info ->
    env_contracts mid caddr <> None ->
    deployment_info Setup (snoc trace step) caddr = Some dep_info.
  Proof.
    intros Hdep Hdeployed.
    cbn.
    destruct_chain_step; auto.
    - destruct_action_eval; cbn; auto.
      destruct (address_eqb_spec to_addr caddr) as [Heq | Hneq].
      + (* to_addr is fixed by countable.choose, so rewrite with Heq instead of subst *)
        exfalso.
        apply Hdeployed.
        congruence.
      + auto.
    - destruct_action_eval; cbn; auto.
      destruct (address_eqb_spec to_addr caddr) as [Heq | Hneq].
      + (* to_addr is fixed by countable.choose, so rewrite with Heq instead of subst *)
        exfalso.
        apply Hdeployed.
        congruence.
      + auto.
  Qed.

  Lemma CStr_dep_info_preserve {Setup : Type} `{ser_setup : Serializable Setup}
      (str : ChainStream) {i} {caddr} {dep_info} :
    deployment_info Setup (CStr_clist str i) caddr = Some dep_info ->
    forall j,
      (i <= j)%nat ->
      deployment_info Setup (CStr_clist str j) caddr = Some dep_info.
  Proof.
    intros Hdep j Hij.
    induction Hij as [|j Hij IH].
    - exact Hdep.
    - rewrite CStr_clist_snoc.
      eapply deployment_info_snoc_preserve.
      + exact IH.
      + pose proof
          (deployment_info_env_contracts_some
             (CStr_clist str i) caddr dep_info Hdep)
          as Hdeployed_i.
        destruct (env_contracts (CStr_nth i str) caddr) as [wc|] eqn:Hwc.
        * rewrite (CStr_wc_preserve str Hwc j Hij).
          discriminate.
        * contradiction.
  Qed.

  Local Ltac destruct_msg_in_action_eq :=
    repeat
      match goal with
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
      | H : act_deploy _ _ _ =
              match ?msg with
              | Some _ => act_call _ _ _
              | None => act_transfer _ _
              end |- _ =>
          destruct msg; cbn in H; discriminate
      | H : match ?msg with
            | Some _ => act_call _ _ _
            | None => act_transfer _ _
            end = act_deploy _ _ _ |- _ =>
          destruct msg; cbn in H; discriminate
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

  Local Ltac invert_action_eq :=
    repeat
      match goal with
      | H1 : ?act = build_act _ _ _ _,
        H2 : ?act = build_act _ _ _ _ |- _ =>
          rewrite H1 in H2; inversion H2; subst; clear H2
      | H : build_act _ _ _ _ = build_act _ _ _ _ |- _ =>
          inversion H; subst; clear H
      | H : act_transfer _ _ = act_transfer _ _ |- _ =>
          inversion H; subst; clear H
      | H : act_call _ _ _ = act_call _ _ _ |- _ =>
          inversion H; subst; clear H
      | H : act_deploy _ _ _ = act_deploy _ _ _ |- _ =>
          inversion H; subst; clear H
      | H : act_transfer _ _ = act_call _ _ _ |- _ => discriminate H
      | H : act_call _ _ _ = act_transfer _ _ |- _ => discriminate H
      | H : act_transfer _ _ = act_deploy _ _ _ |- _ => discriminate H
      | H : act_deploy _ _ _ = act_transfer _ _ |- _ => discriminate H
      | H : act_call _ _ _ = act_deploy _ _ _ |- _ => discriminate H
      | H : act_deploy _ _ _ = act_call _ _ _ |- _ => discriminate H
      | H : Some _ = Some _ |- _ =>
          inversion H; subst; clear H
      | H : existT _ _ _ = existT _ _ _ |- _ =>
          inversion H; subst; clear H
      end;
    destruct_msg_in_action_eq.

  Local Ltac solve_contract_addr_contradiction Hreach :=
    match goal with
    | Hc : env_contracts _ ?addr = Some ?wc,
      Hn : address_is_contract ?addr = false |- _ =>
        let Hfmt := fresh "Haddr_format" in
        pose proof (contract_addr_format addr wc Hreach Hc) as Hfmt;
        congruence
    | Hn : address_is_contract ?addr = false,
      Hc : env_contracts _ ?addr = Some ?wc |- _ =>
        let Hfmt := fresh "Haddr_format" in
        pose proof (contract_addr_format addr wc Hreach Hc) as Hfmt;
        congruence
    end.

  Local Ltac solve_eval_incoming Hreach :=
    subst; cbn in *;
    invert_action_eq;
    try solve_contract_addr_contradiction Hreach;
    invert_action_eq;
    try solve_contract_addr_contradiction Hreach;
    try congruence;
    try reflexivity.

  Local Lemma chain_step_incoming_calls_eq_reachable
        {Msg : Type} `{Serializable Msg}
        {origin from to : ChainState}
        (trace : ChainTrace origin from)
        (caddr : Address)
        (step1 step2 : ChainStep from to) :
    reachable from ->
    incoming_calls Msg (snoc trace step1) caddr =
    incoming_calls Msg (snoc trace step2) caddr.
  Proof.
    intro Hreach.
    cbn.
    do 2 destruct_chain_step;
      auto;
      try solve [rewrite_queue; discriminate];
      rewrite_queue.
    - inversion queue_prev0; subst; clear queue_prev0.
      do 2 destruct_action_eval; solve_eval_incoming Hreach.
      destruct msg; destruct msg0; try congruence; inversion H5; auto.
    - inversion queue_prev0; subst; clear queue_prev0.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.
    - inversion queue_prev0; subst; clear queue_prev0.
      exfalso.
      eapply action_trace_finish_fail_absurd
        with (st := from)
             (finish := finish_bstate)
             (fail := fail_bstate)
             (act := act0)
             (acts := chain_state_queue finish_bstate)
             (act' := act')
             (acts' := acts'); eauto.
      replace (chain_state_queue finish_bstate) with ([] ++ chain_state_queue finish_bstate)
        in H2 by auto.
      apply list_app_eq_tl in H2. subst. auto.
    - inversion queue_prev0; subst; clear queue_prev0.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.
    - inversion queue_prev0; subst; clear queue_prev0.
      do 2 destruct_action_eval; solve_eval_incoming Hreach.
      destruct msg; destruct msg0; try congruence; inversion H4; auto.
    - inversion queue_prev0; subst; clear queue_prev0.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.
    - inversion queue_prev0; subst; clear queue_prev0.
      exfalso.
      eapply action_trace_finish_fail_absurd
        with (st := from)
             (finish := finish_bstate)
             (fail := fail_bstate); eauto.
    - inversion queue_prev0; subst; clear queue_prev0.
      unfold act_is_from_account, act_is_from_contract in *.
      congruence.
  Qed.

  Lemma cstr_clist_step_incoming_calls  {Msg : Type} `{Serializable Msg}
      {caddr} {i : nat} {str}
        (start : CStr_nth 0 str = empty_state)
        (step : ChainStep (CStr_nth i str) (CStr_nth (S i) str)):
    incoming_calls Msg (CStr_clist str (S i)) caddr =
      incoming_calls Msg (snoc (CStr_clist str i) step) caddr.
  Proof.
    rewrite CStr_clist_snoc.
    eapply chain_step_incoming_calls_eq_reachable.
    apply CStr_nth_reachable.
    exact start.
  Qed.

End ChainStream.

Ltac cstr_destruct_deployed_typed :=
  match goal with
  | H_start : @CStr_nth _ _ 0 ?str1 = empty_state,
    H_dep : env_contracts _ ?caddr = Some ?contract |- _ =>
    match type of H_dep with
    | context [ @CStr_nth _ _ ?j ?str2 ] =>
      unify str1 str2;
      let h_dt := fresh "Hdeployed_typed" in
      let d_info := fresh "dep_info" in
      let c_st := fresh "cstate" in
      let i_calls := fresh "inc_calls" in
      let h_di := fresh "Hdep_info" in
      let h_cs := fresh "Hcstate" in
      let h_ic := fresh "Hinc_calls" in
      pose proof (deployed_typed (CStr_clist_start str1 H_start j) H_dep) as h_dt;
      rewrite CStr_deploy_info_eq, CStr_incoming_calls_eq in h_dt;
      specialize h_dt as (d_info & c_st & i_calls & h_di & h_cs & h_ic)
    end
  end.

Ltac cstr_destruct_deployed_typed_manual j :=
  match goal with
  | H_start : @CStr_nth _ _ 0 ?str1 = empty_state,
    H_dep : env_contracts _ ?caddr = Some ?contract |- _ =>
    match type of H_dep with
    | context [ @CStr_nth _ _ j ?str2 ] =>
      unify str1 str2;
      let h_dt := fresh "Hdeployed_typed" in
      let d_info := fresh "dep_info" in
      let c_st := fresh "cstate" in
      let i_calls := fresh "inc_calls" in
      let h_di := fresh "Hdep_info" in
      let h_cs := fresh "Hcstate" in
      let h_ic := fresh "Hinc_calls" in
      pose proof (deployed_typed (CStr_clist_start str1 H_start j) H_dep) as h_dt;
      rewrite CStr_deploy_info_eq, CStr_incoming_calls_eq in h_dt;
      specialize h_dt as (d_info & c_st & i_calls & h_di & h_cs & h_ic)
    end
  end.

From Stdlib Require Import Streams.

Section TraceToStream.
  Context {BaseTypes : ChainBase}.

  Definition ChainStepNext : Type :=
    forall st : ChainState, reachable st -> { st' : ChainState & ChainStep st st' }.

  Lemma reachable_next (st st' : ChainState) : reachable st -> ChainStep st st' -> reachable st'.
  Proof. intros [tr] step. constructor. exact (snoc tr step). Qed.

  Variable next : ChainStepNext.

  CoFixpoint ext_stream (st : ChainState) (H : reachable st) : Stream ChainState :=
    Cons st (ext_stream (projT1 (next st H)) (reachable_next st _ H (projT2 (next st H)))).

  Fixpoint ext_path (n : nat) :
      forall (st : ChainState) (H : reachable st),
        ChainStep (Str_nth n (ext_stream st H)) (Str_nth (S n) (ext_stream st H)) :=
    match n with
    | 0 => fun st H => projT2 (next st H)
    | S k => fun st H =>
        ext_path k (projT1 (next st H)) (reachable_next st _ H (projT2 (next st H)))
    end.

  Fixpoint prep {from to : ChainState} (tr : ChainTrace from to) (rest : Stream ChainState)
      : Stream ChainState :=
    match tr with
    | @clnil _ _ p => Cons p rest
    | @snoc _ _ _ _ to' tr' _ => prep tr' (Cons to' rest)
    end.

  Fixpoint prep_path {from to : ChainState} (tr : ChainTrace from to) :
      forall (rest : Stream ChainState),
        StreamPath (Cons to rest) -> StreamPath (prep tr rest) :=
    match tr as tr0 in ChainedList _ _ f t
          return forall rest, StreamPath (Cons t rest) -> StreamPath (prep tr0 rest) with
    | @clnil _ _ p => fun rest pth => pth
    | @snoc _ _ _ mid to' tr' step => fun rest pth =>
        prep_path tr' (Cons to' rest)
          (fun n =>
             match n as n0
                   return ChainStep (Str_nth n0 (Cons mid (Cons to' rest)))
                                    (Str_nth (S n0) (Cons mid (Cons to' rest))) with
             | 0 => step
             | S k => pth k
             end)
    end.

  Fixpoint trace_length {from to : ChainState} (tr : ChainTrace from to) : nat :=
    match tr with
    | clnil => 0
    | snoc tr' _ => S (trace_length tr')
    end.

  Lemma prep_nth_0 {from to : ChainState} (tr : ChainTrace from to) rest :
    Str_nth 0 (prep tr rest) = from.
  Proof.
    revert rest. induction tr as [p|from' mid to' tr' IH step]; intros rest; [reflexivity|].
    cbn [prep]. apply IH.
  Qed.

  Lemma prep_nth_length {from to : ChainState} (tr : ChainTrace from to) rest k :
    Str_nth (trace_length tr + k) (prep tr rest) = Str_nth k (Cons to rest).
  Proof.
    revert rest k. induction tr as [p|from' mid to' tr' IH step]; intros rest k; [reflexivity|].
    cbn [prep trace_length]. rewrite plus_Sn_m, plus_n_Sm. apply IH.
  Qed.

  Lemma prep_path_length {T : Type} (obs : forall a b : ChainState, ChainStep a b -> T)
      {from to : ChainState} (tr : ChainTrace from to) rest pth k :
    obs _ _ (prep_path tr rest pth (trace_length tr + k)) = obs _ _ (pth k).
  Proof.
    revert rest pth k. induction tr as [p|from' mid to' tr' IH step]; intros rest pth k; [reflexivity|].
    cbn [prep_path trace_length].
    rewrite plus_Sn_m, plus_n_Sm. apply IH with (k := S k).
  Qed.

  Lemma prep_clist_agree {R : Type}
      (F : forall a b : ChainState, ChainTrace a b -> R)
      (G : forall a b : ChainState, ChainStep a b -> R -> R) (c : R)
      (Fnil : forall a, F a a clnil = c)
      (Fsnoc : forall a m b (t : ChainTrace a m) (l : ChainStep m b), F a b (snoc t l) = G m b l (F a m t))
      {from to : ChainState} (tr : ChainTrace from to) rest pth :
    F _ _ (CStr_clist (@existT (Stream ChainState) StreamPath (prep tr rest) (prep_path tr rest pth)) (trace_length tr)) = F _ _ tr.
  Proof.
    revert rest pth. induction tr as [p|from' mid to' tr' IH step]; intros rest pth.
    - cbn. rewrite !Fnil. reflexivity.
    - cbn [trace_length CStr_clist nat_rect prep prep_path]. cbn.
      rewrite Fsnoc, Fsnoc.
      set (pth' := fun n =>
             match n as n0
                   return ChainStep (Str_nth n0 (Cons mid (Cons to' rest)))
                                    (Str_nth (S n0) (Cons mid (Cons to' rest))) with
             | 0 => step
             | S k => pth k
             end).
      specialize (IH (Cons to' rest) pth').
      pose proof (prep_path_length (fun a b l => G a b l) tr' (Cons to' rest) pth' 0) as Hstep.
      rewrite <- plus_n_O in Hstep. cbn in Hstep.
      rewrite Hstep. f_equal. exact IH.
  Qed.

  Definition deployment_info_step (Setup : Type) `{Serializable Setup} (caddr : Address)
      (m b : ChainState) (l : ChainStep m b) (x : option (DeploymentInfo Setup))
      : option (DeploymentInfo Setup) :=
    match l with
    | step_action_user _ _ _ _ _ _ _ (eval_deploy limit origin from to amount _ setup _ _ _ _ _ _ _ _ _ _) _ _ _ _
    | step_action_contract _ _ _ _ _ _ (eval_deploy limit origin from to amount _ setup _ _ _ _ _ _ _ _ _ _) _ _ =>
      if (to =? caddr)%address then
        match deserialize setup with
        | Some setup => Some (build_deployment_info origin from amount setup)
        | None => None
        end
      else x
    | _ => x
    end.

  Lemma stream_through_trace (bstate : ChainState) (tr : ChainTrace empty_state bstate) :
    exists (str : ChainStream) (start : CStr_nth 0 str = empty_state) (n : nat),
      CStr_nth n str = bstate /\
      (forall (Setup : Type) (ser : Serializable Setup) (caddr : Address),
         deployment_info Setup (CStr_clist str n) caddr = deployment_info Setup tr caddr).
  Proof.
    set (R := inhabits tr : reachable bstate).
    set (st1 := projT1 (next bstate R)).
    set (R1 := reachable_next bstate st1 R (projT2 (next bstate R))).
    set (rest := ext_stream st1 R1).
    set (pth := fun n =>
           match n as n0 return ChainStep (Str_nth n0 (Cons bstate rest)) (Str_nth (S n0) (Cons bstate rest)) with
           | 0 => projT2 (next bstate R)
           | S k => ext_path k st1 R1
           end).
    exists (@existT (Stream ChainState) StreamPath (prep tr rest) (prep_path tr rest pth)).
    exists (prep_nth_0 tr rest).
    exists (trace_length tr).
    split.
    - unfold CStr_nth. cbn [projT1].
      pose proof (prep_nth_length tr rest 0) as H. rewrite <- plus_n_O in H. exact H.
    - intros Setup ser caddr.
      apply (prep_clist_agree (fun a b t => deployment_info Setup t caddr)
               (deployment_info_step Setup caddr) None); [reflexivity|].
      intros a m b t l. reflexivity.
  Qed.

End TraceToStream.
