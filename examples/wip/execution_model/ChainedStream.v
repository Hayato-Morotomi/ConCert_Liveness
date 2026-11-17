From ConCert.Utils Require Import Automation.
From Stdlib Require Import Streams.
From Stdlib Require Import Lia.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From Stdlib Require Import ZArith.

Section ChainedStream.
  Context {Point : Type} {Link : Point -> Point -> Type}.

  Definition StreamPath (str : Stream Point) : Type :=
    forall n, Link (Str_nth n str) (Str_nth (S n) str).

  Definition ChainedStream : Type :=
    { str : Stream Point & StreamPath str}.

  Definition CStr_hd (cs : ChainedStream) : Point :=
    hd (projT1 cs).

  Definition CStr_tl (cs : ChainedStream) : ChainedStream.
  Proof.
    destruct cs as [str path].
    exists (tl str).
    intro n.
    exact (path (S n)).
  Defined.

  Fixpoint CStr_nth_tl (n : nat) (cs : ChainedStream) : ChainedStream :=
    match n with
    | O => cs
    | S m => CStr_nth_tl m (CStr_tl cs)
    end.

  Definition CStr_nth n (cs : ChainedStream) : Point :=
    Str_nth n (projT1 cs).

  Definition CStr_link (str : ChainedStream) (n : nat)
    : Link (CStr_nth n str) (CStr_nth (S n) str).
  Proof.
    pose (projT2 str) as path. specialize (path n). auto.
  Defined.

  Definition CStr_clist (str : ChainedStream) (n : nat)
    : ChainedList Point Link (CStr_nth 0 str) (CStr_nth n str).
  Proof.
    induction n.
    - constructor.
    - unfold CStr_nth in *.
      destruct str as (str & path). cbn in *.
    apply (snoc IHn (path n)).
  Defined.

  Definition CStr_clist_start {p : Point}
    (str : ChainedStream) (start : CStr_nth 0 str = p) (n : nat)
     : ChainedList Point Link p (CStr_nth n str).
  Proof.
    induction n; subst p.
    - constructor.
    - unfold CStr_nth in *.
      destruct str as (str & path). cbn in *.
    apply (snoc IHn (path n)).
  Defined.

  Definition CStr_clist_n_m
    (str : ChainedStream) (n m: nat) (Hnm : (n <= m)%nat)
     : ChainedList Point Link (CStr_nth n str) (CStr_nth m str).
  Proof.
    destruct (Nat.eq_dec n m).
    { subst. constructor. }
    induction m.
    - assert (n = 0)%nat by lia. subst. constructor.
    - assert (n <= m)%nat by lia.
      destruct (Nat.eq_dec n m); subst.
      * destruct str as (str & path). cbn in *.
        apply (snoc clnil (path m)).
      * destruct str as (str & path). cbn in *.
        specialize_hypotheses.
        apply (snoc IHm (path m)).
  Defined.

  Lemma cstr_tl_nth_tl : forall (n:nat) (s:ChainedStream),
    CStr_tl (CStr_nth_tl n s) = CStr_nth_tl n (CStr_tl s).
  Proof.
    induction n; cbn; auto.
  Qed.

  Lemma CStr_nth_tl_plus : forall (n m:nat) (str:ChainedStream),
    CStr_nth_tl n (CStr_nth_tl m str) = CStr_nth_tl (n + m) str.
  Proof.
    intros n.
    induction n as [| n IHn]; auto.
    intros m str.  cbn.
    enough (H : CStr_tl (CStr_nth_tl m str) = CStr_nth_tl m (CStr_tl str)).
    { rewrite H.
      apply IHn. }
    revert str.
    induction m as [| m IHm]; intro str.
    - reflexivity.
    - simpl. apply IHm.
  Qed.

  Lemma CStr_nth_tl_0 i str :
    CStr_nth 0 (CStr_nth_tl i str) = CStr_nth i str.
  Proof.
    unfold CStr_nth, Str_nth. generalize str.
    induction i as [| m IHm]; auto.
    intros s. cbn in *. rewrite IHm. destruct s. auto.
  Qed.

  Lemma CStr_clist_snoc str i :
    CStr_clist str (S i) = snoc (CStr_clist str i) (CStr_link str i).
  Proof.
    destruct str as [s path].
    reflexivity.
  Qed.

End ChainedStream.