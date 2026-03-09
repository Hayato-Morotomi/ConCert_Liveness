(* 
  20260108

*)

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
From ConCert.Examples.Wip.General Require Import Agreement.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Relations.Relation_Operators.
From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import ChainStreamProperty.

Section RankingLiveness.

  Context {BaseTypes : ChainBase}.
  
  Lemma Liveness_rank_opt_first_bottom
      {Setup Msg State Error : Type}
      `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}
      {A : Type}
      (R : A -> A -> Prop)
      (wfR : well_founded R)
      (bot : A)
      (eq_decA : forall x y : A, {x = y} + {x <> y})
      (f : Address -> ChainState -> option A)
      (P : Address -> ChainState -> Prop)
    :
      forall (caddr : Address) (bstate_from : ChainState),
        (* start_some *)
        (exists v, 
          f caddr bstate_from = Some v /\
          (v = bot -> P caddr bstate_from)) -> 
        (* eventually decrease *)
        (forall bstate v1,
            reachable_through bstate_from bstate ->
            f caddr bstate = Some v1 ->
            v1 <> bot ->
            forall (str : ChainStream),
              Str_nth 0 str = bstate ->
              path str ->
              exists i v2,
                f caddr (Str_nth i str) = Some v2 /\
                R v2 v1) ->
        (* first bottom *)
        (forall prev next,
            reachable_through bstate_from prev ->
            ChainStep prev next ->
            f caddr prev <> Some bot ->
            f caddr next = Some bot ->
            P caddr next) ->
        (* statement *)
        reachable bstate_from ->
        forall (str : ChainStream),
          path str ->
          Str_nth 0 str = bstate_from ->
          exists n, P caddr (Str_nth n str).
  Proof.
    intros caddr bstate_from (v0 & Hv0 & Hstartbot) Hevdec Hfirst Hreach str Hpath Hstart.
    
    assert (Hf0 : f caddr (Str_nth 0 str) = Some v0) by (rewrite Hstart; exact Hv0).

    
    set (ReachBot := fun (v : A) =>
      forall i,
        f caddr (Str_nth i str) = Some v ->
        exists k, f caddr (Str_nth (i + k) str) = Some bot).

    assert (HReachBot0 : ReachBot v0).
    {
      refine (well_founded_induction wfR (fun v => ReachBot v) _ _).
      intros v IH i Hfi.
      destruct (eq_decA v bot) as [-> | Hneq].
      - exists 0%nat. now rewrite Nat.add_0_r.
      - 
        pose (sti := Str_nth i str).
        assert (Hrt : reachable_through bstate_from sti).
        { subst sti. eapply reachable_through_stream; eauto. }

        set (str_i := Str_nth_tl i str).
        assert (H0_i : Str_nth 0 str_i = sti).
        { subst str_i sti. rewrite Str_nth_plus. now cbn. }

        assert (Hpath_i : path str_i).
        { unfold str_i. apply stream_path_nth_tl; auto. }

        destruct (Hevdec sti v Hrt Hfi Hneq str_i H0_i Hpath_i)
          as [j [v2 [Hfj HR]]].

        
        assert (Hf_ij : f caddr (Str_nth (i + j) str) = Some v2).
        { subst str_i. rewrite Str_nth_plus in Hfj. rewrite Nat.add_comm; auto. }
        destruct (IH v2 HR (i + j)%nat Hf_ij) as [k Hk].
        exists (j + k)%nat.
        replace (i + (j + k))%nat with ((i + j) + k)%nat by lia. auto.
    }
    destruct (HReachBot0 0%nat Hf0) as [k Hkbot].

    
    set (pb := fun t => f caddr (Str_nth t str) = Some bot).

    
    assert (opt_eq_dec : forall (x y : option A), {x = y} + {x <> y}).
    {
      intros [x|] [y|].
      - destruct (eq_decA x y) as [->|Hne]; [left; reflexivity|right; intro H3; inversion H3; auto].
      - right; discriminate.
      - right; discriminate.
      - left; reflexivity.
    }

    assert (pb_dec : forall t, {pb t} + {~ pb t}).
    {
      intro t. unfold pb.
      destruct (opt_eq_dec (f caddr (Str_nth t str)) (Some bot)) as [H3|H3].
      - left; auto.
      - right; auto.
    }

    
    assert (Hex_first :
      exists m,
        pb m /\ m <= k /\ (m = 0 \/ ~ pb (Nat.pred m))).
    {
      induction k as [|k IH].
      - exists 0%nat. split; [exact Hkbot|]. split; [lia|left; reflexivity].
      - 
        assert (Hpbs : pb (S k)) by (cbn in Hkbot; auto).
        destruct (pb_dec k) as [Hpk | HnPk].
        + 
          destruct IH as [m [Hpm [Hle Hbd]]]; cbn; auto.
          exists m. split; [exact Hpm|]. split; [lia| exact Hbd].
        + 
          exists (S k). split; [exact Hpbs|].
          split; [lia|].
          right. cbn. exact HnPk.
    }
    destruct Hex_first as [m [Hpm [Hle Hbd]]].
    
    destruct m as [|m'].
    - (* m=0 *)
      exists 0%nat.
      rewrite Hstart.
      apply Hstartbot. unfold pb in Hpm. rewrite Hf0 in Hpm. inversion Hpm. auto.
    - (* m = S m' *)
      exists (S m')%nat.
      pose (prev := Str_nth m' str).
      pose (next := Str_nth (S m') str).

      (* ChainStep prev next *)
      assert (inhabited (ChainStep prev next)) as [Hstep].
      { subst prev next. specialize (Hpath m'). rewrite Nat.add_comm in Hpath; cbn in Hpath; auto. }

      assert (Hrt_prev : reachable_through bstate_from prev).
      { subst prev. eapply reachable_through_stream; eauto. }

      destruct Hbd; try congruence.
      apply Hfirst with (prev := prev); auto.
  Qed.

  Definition liveness bstate_from
        (P : forall (bstate : ChainState), Prop) : Prop :=
    forall (str : ChainStream),
      path str ->
      Str_nth 0 str = bstate_from ->
      exists (n : nat),  
        P (Str_nth n str).

End RankingLiveness.

Ltac proof_liveness f bot :=
  match goal with
  | deployed : env_contracts _ ?caddr = Some _ 
    |- liveness ?bstate_from ?P => 
    cbv [liveness];
    let str := fresh "str" in
    intros str Hpath Hstart;
    pattern caddr;
    change (exists (n : nat),
      (fun (a : Address) => P)
      caddr
      (Str_nth n str)) ;
    eapply Liveness_rank_opt_first_bottom 
        with (f := f) (bot := bot); subst bot; eauto
  end.