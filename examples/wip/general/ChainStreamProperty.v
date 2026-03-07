





From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify.
From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Streams.
From Stdlib Require Import Basics.
From Stdlib Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.

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

Section ChainTracePropertyAgain.
  Context {Base : ChainBase}.

  Lemma action_end bstate a l :
    bstate.(chain_state_queue) = a :: l ->
    exists bstate',
      bstate'.(chain_state_queue) = l /\
      inhabited (ChainStep bstate bstate').
  Proof.
  Abort.

  
  Lemma step_action_equiv {prev next1 next2 : ChainState} : 
    reachable prev ->
    prev.(chain_height) = next1.(chain_height) ->
    prev.(chain_height) = next2.(chain_height) ->
    ChainStep prev next1 ->
    ChainStep prev next2 ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * reach Hheight1 Hheight2 step1 step2. 
    assert (reach1 : reachable next1) by (eapply reachable_step; eauto).
    assert (reach2 : reachable next2) by (apply (reachable_step prev next2); eauto).
    specialize (queue_from_account prev reach) as from_accs.
    repeat destruct_chain_step; cbn in *; subst; 
      try destruct (valid_header); 
      try rewrite_environment_equiv; cbn in *; try lia; try congruence.
    - (* valid - valid *)
      rewrite_queue. inversion_subst queue_prev0.
      apply Forall_cons_iff in from_accs as (from_acc & from_accs).
      split; auto.
      specialize (action_trace_no_branch action_trace0 action_trace ltac:(auto))
        as [(next2' & trace & env_eq & queue_eq) | (next1' & trace & env_eq & queue_eq)].
      + 
        rewrite_queue.
        destruct (action_trace_step trace) as [|(mid & [step] & [trace'])]; subst.
        * rewrite_environment_equiv. reflexivity.
        * (* contra *)
          assert (reach_at : reachable_in_action_trace next1 next1). apply reachable_in_action_trace_refl; auto. 
          assert (reach_at_mid : reachable_in_action_trace next1 mid). 
          { eapply reachable_in_action_trace_step; eauto. }
          destruct_action_chain_step. rewrite_queue.
          specialize (emited_acts_from_is_always_contract reach_at queue_prev0 eval) as from_contracts.
          specialize (action_trace_drop_le reach_at_mid trace') as Hle.
          rewrite_queue.
          rewrite no_drop_from_account, drop_until_from_account in Hle; eauto. 
          cbn in *. lia. apply Forall_cons_iff in from_accs as (_ & ?); auto.
      + 
        rewrite_queue.
        destruct (action_trace_step trace) as [|(mid & [step] & [trace'])]; subst.
        * rewrite_environment_equiv. reflexivity.
        * (* contra *)
          assert (reach_at : reachable_in_action_trace next2 next2). apply reachable_in_action_trace_refl; auto. 
          assert (reach_at_mid : reachable_in_action_trace next2 mid). 
          { eapply reachable_in_action_trace_step; eauto. }
          destruct_action_chain_step. rewrite_queue.
          specialize (emited_acts_from_is_always_contract reach_at queue_prev0 eval) as from_contracts.
          specialize (action_trace_drop_le reach_at_mid trace') as Hle.
          rewrite_queue. rewrite <- H1 in *.
          rewrite no_drop_from_account, drop_until_from_account in Hle; eauto. 
          cbn in *. lia. apply Forall_cons_iff in from_accs as (_ & ?); auto.
    - (* invalid - valid *)
      rewrite_queue. inversion_subst queue_prev0. specialize_hypotheses. auto.
    - (* valid - invalid *)
      rewrite_queue. inversion_subst queue_prev0. 
      specialize (no_action_trace next1). specialize_hypotheses. auto.
    - (* invalid - invalid *)
      rewrite_queue. inversion_subst queue_prev0. split; auto.
  Qed.

  
  Lemma step_action_equiv_equiv {prev1 prev2 next1 next2 : ChainState} : 
    ChainStep prev1 next1 ->
    ChainStep prev2 next2 ->
    reachable prev1 ->
    reachable prev2 ->
    EnvironmentEquiv prev1 prev2 ->
    prev1.(chain_state_queue) = prev2.(chain_state_queue) ->
    prev1.(chain_height) = next1.(chain_height) ->
    prev2.(chain_height) = next2.(chain_height) ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    















































  Abort.

  Inductive ChainTraceEquiv
    : (forall {from1 from2 to1 to2}, 
        ChainTrace from1 to1 -> ChainTrace from2 to2 -> Prop) :=
  | tr_equiv_clnil {p1 p2 : ChainState} : 
      ChainTraceEquiv (@clnil ChainState ChainStep p1) 
                            (@clnil ChainState ChainStep p2)
  | tr_equiv_snoc {from1 from2 mid1 mid2 to1 to2 : ChainState} 
                  {trace1 : ChainTrace from1 mid1} 
                  {trace2 : ChainTrace from2 mid2} 
                  {step1 : ChainStep mid1 to1} 
                  {step2 : ChainStep mid2 to2} :
      EnvironmentEquiv to1 to2 ->
      to1.(chain_state_queue) = to2.(chain_state_queue) ->
      ChainTraceEquiv trace1 trace2 ->
      ChainTraceEquiv (snoc trace1 step1) (snoc trace2 step2).

End ChainTracePropertyAgain.

Section ChainStreamProperty.
  Context {Base : ChainBase}.

  Definition ChainStream := Stream ChainState.

  Definition path stream : Prop := forall n, 
    inhabited (ChainStep (Str_nth n stream) (Str_nth (n + 1) stream)).

  Lemma stream_path_nth_tl {n} {str} :
    path str -> path (Str_nth_tl n str).
  Proof.
    unfold path.
    intros Hpath k.
    rewrite !Str_nth_plus.
    replace ((k + 1) + n) with ((k + n) + 1) by lia.
    exact (Hpath (k + n)).
  Qed.

  Lemma stream_reahchable_through : forall bstate str i,
    reachable bstate ->
    path str ->
    Str_nth 0 str = bstate ->
    reachable_through bstate (Str_nth i str).
  Proof.
    unfold path, reachable_through.
    induction i; intros reach Hpath Hstart; split; auto.
    - subst. repeat constructor.
    - repeat (specialize (IHi ltac:(auto))).
      destruct IHi as (_ & [trace]).
      specialize (Hpath i) as [step].
      constructor. rewrite Nat.add_1_r in *.
      eapply (snoc trace step).
  Qed. 

  Lemma stream_reahcable : forall bstate str i,
    reachable bstate ->
    path str ->
    Str_nth 0 str = bstate ->
    reachable (Str_nth i str).
  Proof.
    intros.
    eapply reachable_through_reachable.
    eapply stream_reahchable_through; eauto.
  Qed.

  Fixpoint trace_length {from to} (trace : ChainTrace from to) : nat :=
    match trace with
    | clnil => 0%nat
    | snoc trace' _ => S (trace_length trace')
    end.
  
  Fixpoint trace_nth_inner default (n:nat)
     {from to} (trace : ChainTrace from to) : ChainState :=
    match n, trace with
      | O, @snoc _ _ _ _ to _ _ => to
      | O, @clnil _ _ p => p
      | S m, clnil => default
      | S m, snoc trace' _ => trace_nth_inner default m trace'
    end.

  Definition trace_nth' default (n:nat) {from to} (trace : ChainTrace from to) 
    : ChainState :=
    let len := trace_length trace in
    if (len <? n) then default
      else trace_nth_inner default (len - n) trace.

  Lemma trace_nth_from' {default from to} (trace : ChainTrace from to) :
    trace_nth' default 0 trace = from.
  Proof. 
    remember from; induction trace; subst; cbn; auto.
    unfold trace_nth' in *.
    destruct (Nat.ltb_spec (trace_length trace) 0); try lia.
    replace (trace_length trace - 0) with (trace_length trace) in IHtrace by lia. 
    auto.
  Qed. 

  Lemma trace_nth_to {default from to} (trace : ChainTrace from to) :
    trace_nth' default (trace_length trace) trace = to.
  Proof. 
    unfold trace_nth'. rewrite Nat.ltb_irrefl.
    remember from; destruct trace; cbn; auto. 
    replace (trace_length trace - trace_length trace) with 0 by lia.
    auto. 
  Qed.

  Lemma trace_from_step {from to} :
    ChainTrace from to ->
    from = to \/
    exists mid, inhabited (ChainStep from mid) /\ inhabited (ChainTrace mid to).
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

  Lemma trace_nth_1_step {default from to} (trace : ChainTrace from to) :
    0 < trace_length trace ->
    inhabited (ChainStep from (trace_nth' default 1 trace)).
  Proof.
    remember from; induction trace; cbn; try lia; subst.
    destruct trace; subst; cbn in *; auto.
    intros.
    rewrite Nat.sub_0_r in *. apply IHtrace; auto. lia.
  Qed.

  Lemma trace_nth_inner_1step {default from mid to} 
     {step : ChainStep mid to} {trace : ChainTrace from mid} {n} :
    trace_nth_inner default (S n) (snoc trace step) = trace_nth_inner default n trace.
  Proof.
    cbn. auto.
  Qed.

  
  Lemma trace_nth_path default {from to} (trace : ChainTrace from to) :
    forall n, 
      S n <= trace_length trace ->
      inhabited (ChainStep (trace_nth' default n trace) (trace_nth' default (S n) trace)).
  Proof.
    remember from; induction trace; subst; cbn; try lia.
    destruct n as [|n'].
    -
      intros.
      rewrite trace_nth_from'. eapply trace_nth_1_step. cbn. lia.
    - intros.
      unfold trace_nth'. cbn.
      destruct (Nat.leb_spec (S (trace_length trace)) n'); try lia.
      destruct (Nat.leb_spec (trace_length trace) n'); try lia.
      destruct (trace_length trace - S n') eqn:Hlen; try lia.
      + 
        assert (trace_length trace - n' = 1). lia. rewrite H2. cbn.
        destruct trace; cbn; auto.
      +
        assert (trace_length trace - n' = S (S n)). lia. rewrite H2.
        specialize (IHtrace ltac:(auto) (S n') ltac:(lia)).
        unfold trace_nth' in IHtrace. 
        destruct (Nat.ltb_spec (trace_length trace) n'); try lia.
        destruct (Nat.ltb_spec (trace_length trace) (S n')); try lia.
        repeat rewrite trace_nth_inner_1step.
        destruct (Nat.ltb_spec (trace_length trace) (S (S n'))); try lia.
        replace (trace_length trace - S (S n')) with n in IHtrace by lia.
        replace (trace_length trace - S n') with (S n) in IHtrace by lia. 
        auto. 
  Qed.

  Lemma stream_trace_equiv : forall {default} from to (trace : ChainTrace from to) stream,
    reachable from ->
    path stream ->
    Str_nth 0 stream = from ->
    from.(chain_height) = to.(chain_height) ->
    forall n,
      n <= trace_length trace ->
      let st_str := Str_nth n stream in
      let st_tr := trace_nth' default n trace in
      EnvironmentEquiv st_str st_tr /\
      st_str.(chain_state_queue) = st_tr.(chain_state_queue) /\
      st_str.(chain_height) = st_tr.(chain_height).
  (* Proof.
    (* n *)
    intros * reach Hpath Hstart Hheight n. 
    generalize dependent stream.
    generalize dependent to.
    generalize dependent from.
    induction n as [|n' IHn']. 
    {
      (* n = 0 *)
      admit.
    }
    intros.
    pose IHn' as IH.

    specialize (IH from reach to trace ltac:(auto) stream ltac:(auto) ltac:(auto) ltac:(lia))
      as (env_eq & queue_eq & height_eq).

    inversion H.
    - (* st_tr = to *)
      remember from; destruct trace; cbn in *; try lia. subst from0.
      inversion H1. subst n'. clear H H1.
      assert (chain_height from = chain_height mid). admit.
      specialize (IHn' from reach mid trace ltac:(auto) stream).
      specialize_hypotheses.
      subst st_tr. 
      replace (S (trace_length trace)) with (trace_length (snoc trace c)) by (cbn; auto).
      rewrite trace_nth_to.
      unfold path in Hpath. specialize (Hpath (trace_length trace)) as [step'].
      subst st_str. rewrite Nat.add_1_r in step'.
      specialize (step_action_equiv_equiv c step') as Heq.
      specialize_hypotheses.
      assert (reachable mid). eapply reachable_trans; eauto.
      specialize_hypotheses. 
      
      (* rewrite H1 in st_tr. *)
      admit.
    - (* trivial *)
      specialize (trace_nth_path default trace n' ltac:(lia)) as [step].
      unfold path in Hpath. specialize (Hpath n') as [step'].
      rewrite Nat.add_1_r in step'.
      admit. (* chain_step_equiv_equiv, chain_height_eq *)

    remember from; destruct trace; cbn in *; try lia. subst from0.
    assert (chain_height from = chain_height mid). admit.
    assert (n' <= trace_length trace).
    { inversion H; lia. }
    specialize (IH from mid trace ltac:(auto) stream ltac:(auto) ltac:(auto) ltac:(auto)).
    destruct IH as (env_eq & queue_eq & height_eq).
    
  Abort. *)
  Abort.

  Fixpoint trace_nth default (n:nat)
     {from to} (trace : ChainTrace from to) : ChainState :=
    match n, trace with
      | O, @snoc _ _ _ _ to _ _ => to
      | O, @clnil _ _ p => p
      | S m, clnil => default
      | S m, snoc trace' _ => trace_nth default m trace'
    end.

  Lemma trace_nth_from {default from to} (trace : ChainTrace from to) :
    trace_nth default (trace_length trace) trace = from.
  Proof. remember from; induction trace; cbn; auto. Qed. 

  Lemma trace_nth_zero {default from to} (trace : ChainTrace from to) :
    trace_nth default 0 trace = to.
  Proof. remember from; destruct trace; cbn; auto. Qed. 

  Lemma stream_trace_equiv : forall {default} from to (trace : ChainTrace from to) stream,
    path stream ->
    Str_nth 0 stream = from ->
    from.(chain_height) = to.(chain_height) ->
    forall n,
      n <= trace_length trace ->
      let st_str := Str_nth n stream in
      let st_tr := trace_nth default (trace_length trace - n)%nat  trace in
      EnvironmentEquiv st_str st_tr /\
      st_str.(chain_state_queue) = st_tr.(chain_state_queue) /\
      st_str.(chain_height) = st_tr.(chain_height).
  Proof.

    intros default from to trace. 
    remember (trace_length trace) as n.
    generalize dependent to.
    generalize dependent from.
    induction n as [|n' IHn']. 
    {
      (* n = 0 *)
      admit.
    }
    intros.
    pose IHn' as IH.
    remember from; destruct trace; cbn in *; try lia. subst from0.
    inversion Heqn.
    assert (chain_height from = chain_height mid). admit.
    specialize (IH from mid trace ltac:(auto) stream ltac:(auto) ltac:(auto) ltac:(auto)).

    
    (* intros default from to trace.
    remember from; induction trace; subst.
    - cbn. intros.
      destruct n eqn:Hn; try lia.
      cbn. rewrite H0. repeat split; auto.
    - cbn. intros.
      specialize (IHtrace ltac:(auto) stream ltac:(auto) ltac:(auto)).
      assert (chain_height from = chain_height mid). admit.
      pose IHtrace as IH.
      specialize (IH ltac:(auto) (trace_length trace) ltac:(lia)).
      replace (trace_length trace -
               trace_length trace) with (0) in IH by lia.
      rewrite trace_nth_zero in IH.
      destruct IH as (env_eq & queue_eq & height_eq).
      Search (?n <= _ -> _ \/ _) in Nat.
      assert (nat_le_case : n <= (trace_length trace) \/ n = S (trace_length trace)).
      { admit. }
      destruct (nat_le_case) as [Hn | Hn].
      +  *)
    
  Abort.

End ChainStreamProperty.