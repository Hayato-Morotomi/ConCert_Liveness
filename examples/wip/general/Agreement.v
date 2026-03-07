(* 
  CTL.v
  ConCert の Safety と pAG の等価性など
  便宜のため、CTL.v をコピー

  ChainStreamPropertyに依存
*)

From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import BuildUtils_modify.
From ConCert.Examples.Wip.General Require Import ChainTraceProperty.
From ConCert.Examples.Wip.General Require Import ChainStreamProperty.
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

From Stdlib Require Import Logic.Decidable.

Section Characterizations.

  Set Nonrecursive Elimination Schemes.
  Context {BaseTypes : ChainBase}.

Definition cAX (P : ChainState -> Prop) (st : ChainState) : Prop :=
  forall st', ChainStep st st' -> P st'.

  Definition cEX (P : ChainState -> Prop) (st : ChainState) : Prop :=
    exists st', inhabited (ChainStep st st') /\ P st'.

  Inductive cAU (P Q : ChainState -> Prop) (st : ChainState) : Prop :=
  | AU0 : Q st -> cAU P Q st
  | AUs : P st -> (forall st', ChainStep st st' -> cAU P Q st') -> cAU P Q st.

  Inductive cEU (P Q : ChainState -> Prop) (st : ChainState) : Prop :=
  | EU0 : Q st -> cEU P Q st
  | EUs st' : P st -> ChainStep st st' -> cEU P Q st' -> cEU P Q st.

  CoInductive cAG' (P : ChainState -> Prop) : ChainState -> Prop :=
  | AGs' : forall st, P st -> (forall st', ChainStep st st' -> cAG' P st') -> cAG' P st.

  CoInductive cAG (P : ChainState -> Prop) (st : ChainState) : Prop :=
  | AGs : P st -> (forall st', ChainStep st st' -> cAG P st') -> cAG P st.

  CoInductive cEG (P : ChainState -> Prop) (st : ChainState) : Prop :=
  | EGs st' : P st -> ChainStep st st' -> cEG P st' -> cEG P st.

  Inductive cAF (P : ChainState -> Prop) (st : ChainState) : Prop :=
  | AF0 : P st -> cAF P st
  | AFs : (forall st', ChainStep st st' -> cAF P st') -> cAF P st.

  Inductive cEF (P : ChainState -> Prop) (st : ChainState) : Prop :=
  | EF0 : P st -> cEF P st
  | EFs st' : ChainStep st st' -> cEF P st' -> cEF P st.

End Characterizations.

Section Form.
  Context {BaseTypes : ChainBase}.

  Inductive form :=
  | ctl_propvar (prop : forall (caddr : Address) (bstate : ChainState), Prop)
  | ctl_bottom
  | ctl_and  (phi psi : form)
  | ctl_or   (phi psi : form)
  | ctl_impl (phi psi : form)
  | ctl_AX   (phi : form)
  | ctl_EX   (phi : form)
  | ctl_AF   (phi : form)
  | ctl_EF   (phi : form)
  | ctl_AG   (phi : form)
  | ctl_EG   (phi : form)
  | ctl_AU   (phi psi : form)
  | ctl_EU   (phi psi : form).

End Form.

Declare Scope ctl_scope.
Bind Scope ctl_scope with form.

Notation "~' x"     := (ctl_impl x ctl_bottom) (at level 75, right associativity) : ctl_scope.
Notation "x /\' y"  := (ctl_and x y) (at level 80, right associativity) : ctl_scope.
Notation "x \/' y"  := (ctl_or x y) (at level 85, right associativity) : ctl_scope.
Notation "x ->' y"  := (ctl_impl x y) (at level 90, right associativity) : ctl_scope.
Notation "x <->' y" := (ctl_and (ctl_impl x y) (ctl_impl x y)) (at level 95, no associativity) : ctl_scope.
Notation "'AX' x" := (ctl_AX x) (at level 70, right associativity) : ctl_scope.
Notation "'EX' x" := (ctl_EX x) (at level 70, right associativity) : ctl_scope.
Notation "'AG' x" := (ctl_AG x) (at level 70, right associativity) : ctl_scope.
Notation "'EG' x" := (ctl_EG x) (at level 70, right associativity) : ctl_scope.
Notation "'AF' x" := (ctl_AF x) (at level 70, right associativity) : ctl_scope.
Notation "'EF' x" := (ctl_EF x) (at level 70, right associativity) : ctl_scope.
Notation "x 'AU' y" := (ctl_AU x y) (at level 85, right associativity) : ctl_scope.
Notation "x 'EU' y" := (ctl_EU x y) (at level 85, right associativity) : ctl_scope.
Notation "x 'AW' y" := (ctl_or (ctl_AU x y) (ctl_AG x)) (at level 85, right associativity) : ctl_scope.
Notation "x 'EW' y" := (ctl_or (ctl_EU x y) (ctl_EG x)) (at level 85, right associativity) : ctl_scope.
Notation "'ctl' P" := (ctl_propvar P) (at level 70, right associativity) : ctl_scope.
Notation "'ctl_top'" := (ctl_impl ctl_bottom ctl_bottom).

Open Scope ctl_scope.

Section CTL.

  (* Set Nonrecursive Elimination Schemes. *)
  Context {BaseTypes : ChainBase}.

  (* inductive semantics *)
Fixpoint eval (addr : Address) (phi : form) (st : ChainState) : Prop :=
    match phi with
    | ctl_propvar P => P addr st
    | ctl_bottom => False
    | ctl_and x y => eval addr x st /\ eval addr y st
    | ctl_or x y => eval addr x st \/ eval addr y st
    | ctl_impl x y => eval addr x st -> eval addr y st
    | ctl_AX x => cAX (eval addr x) st
    | ctl_EX x => cEX (eval addr x) st
    | ctl_AF x => cAF (eval addr x) st
    | ctl_EF x => cEF (eval addr x) st
    | ctl_AG x => cAG (eval addr x) st
    | ctl_EG x => cEG (eval addr x) st
    | ctl_AU x y => cAU (eval addr x) (eval addr y) st
    | ctl_EU x y => cEU (eval addr x) (eval addr y) st
    end.

  (* ctl_impl が ~ Satisfies addr trace i x \/ Satisfies addr trace i y だと証明できない *)
  Lemma axK : forall (addr : Address) (s t : form) (st : ChainState),
    eval addr (s ->' t ->' s) st.
  Proof. simpl. auto. Qed.

  Lemma axS : forall (addr : Address) (s t u : form) (st : ChainState),
    eval addr ((u ->' s ->' t) ->' (u ->' s) ->' u ->' t) st.
  Proof. simpl. auto. Qed.

  Lemma axDN : forall (addr : Address) (s : form) (st : ChainState),
    eval addr (~' ~' s ->' s) st.
  Proof. 
    simpl. intros *. 
  Abort.

  Lemma axN : forall (addr : Address) (s t : form) (st : ChainState),
    eval addr (AX (s ->' t) ->' AX s ->' AX t) st.
  Proof. 
    simpl. intros * Hs_t Hs. unfold cAX in *. auto.
  Qed.

  (* chain_step_serialのために, reachableが必要 *)
  Lemma axSer : forall (addr : Address) (st : ChainState),
    reachable st ->
    eval addr (~' AX ctl_bottom) st.
  Proof.
    intros * reach. simpl. unfold cAX. intro H. 
    destruct (chain_step_serial st reach) as (st' & [step]).
    eapply H; eauto.
  Qed.

  Lemma axU1 : forall (addr : Address) (s t : form) (st : ChainState),
    eval addr (t ->' s AU t) st.
  Proof. simpl. intros * Ht. apply AU0; auto. Qed.  

  Lemma axU2 : forall (addr : Address) (s t : form) (st : ChainState),
    eval addr (s ->' AX (s AU t) ->' s AU t) st.
  Proof. simpl. unfold cAX. intros * Hs HAX. apply AUs; auto. Qed.

  (* rule of inference *) (* 前件の書き方？ *)
  Lemma rMP : forall (addr : Address) (s t : form),
    (forall (st : ChainState), eval addr s st) ->
    (forall (st : ChainState), eval addr (s ->' t) st) ->
    (forall (st : ChainState), eval addr t st). 
  Proof. simpl. auto. Qed.  

  Lemma rMP_wip : forall (addr : Address) (s t : form) (st : ChainState),
    eval addr s st ->
    eval addr (s ->' t) st ->
    eval addr t st. 
  Proof. simpl. auto. Qed.

  Lemma rNec : forall  (addr : Address) (s : form),
    (forall (st : ChainState), eval addr s st) ->
    (forall (st : ChainState), eval addr (AX s) st).
  Proof.
    intros * Hs. simpl. unfold cAX. auto. 
  Qed. 

  (* 量化 *)
  (* Lemma Nec_wip : forall (addr : Address) (s : form) (st : ChainState),
    Satisfies addr s st -> 
    Satisfies addr (AX s) st.
  Proof.
   simpl. unfold cAX. intros * Hs * step.
  Abort. *)

  Lemma rUI : forall (addr : Address) (s t u : form),
    (forall st : ChainState, eval addr (t ->' u) st )-> 
    (forall st : ChainState, eval addr (s ->' AX u ->' u) st)-> 
    (forall st : ChainState, eval addr (s AU t ->' u) st).
  Proof.
    simpl. unfold cAX. intros * Htu Hsuu * HAU.
    induction HAU as [HAU | Hs HAU]; auto.
  Qed. 

  (* オリジナル *)

  Lemma axG1 : forall (addr : Address) (s : form) (st : ChainState),
    eval addr (AG s ->' s) st.
  Proof. simpl. intros * H. destruct H. auto. Qed.    

  Lemma axG2 : forall (addr : Address) (s : form) (st : ChainState),
    eval addr (EG s ->' s) st.
  Proof. simpl. intros * H. destruct H. auto. Qed.
  
  (* chain_step_serialのために, reachableが必要 *)
  Lemma axD : forall (s : form) (addr : Address) (st : ChainState),
    reachable st ->
    eval addr (AX s ->' EX s) st.
  Proof. 
    simpl. unfold cAX, cEX. intros * reach HAX.
    destruct (chain_step_serial st reach) as (st' & [step]).
    exists st'. split; auto. 
  Qed.

  Lemma rAG_ind : forall (s t : form) (addr : Address),
    (forall st : ChainState, eval addr (t ->' s) st )->
    (forall st : ChainState, eval addr (t ->' AX t) st) ->
    (forall st : ChainState, eval addr (t ->' AG s) st).
  Proof.
    intros * H1 H2.
    cofix IH.
    cbn. intros * Ht.
    apply AGs. (* 余帰納型のコンストラクタを適用 *)
    - eapply (rMP_wip addr t s); eauto.
    - intros * step.
      cbn in *.
      apply IH. (* 余帰納法の仮定 *)  
      eapply H2; eauto.
  Qed.  

Section PathSemantics.

  (** ** Path Characterizations *)
  (* Implicit Type (pi : nat -> ChainState). *)
  (* Definition ChainStream := Stream ChainState. *)

  Implicit Type (str : ChainStream).

  (* Definition path str : Prop := 
    forall n, inhabited (ChainStep (Str_nth n str) (Str_nth (n + 1) str)). *)

  (* nil の際は x *)
  (* 
    Definition pcons x pi k := if k is k.+1 then pi k else x.
  *)
  (* Definition pcons x str (k : nat) : ChainState :=
    match k with
    | O => x
    | S k' => Str_nth k' str
    end. *)
  Definition pcons x str := Cons x str.

  (* Definition ptail k str := Str_nth (k + 1) str. *)
  Definition ptail str :=
    match str with
    | Cons _ tl => tl
    end.

  Lemma path_pcons x str : 
    ChainStep x (Str_nth 0 str) -> path str -> path (pcons x str).
  Proof.
    intros H1 H2 [|k]. 
    - cbn in *.
      unfold Str_nth in *. cbn in *. auto.
    - unfold path, Str_nth in *. cbn in *. auto.
  Qed.
  
  Lemma path_ptail str : path str -> path (ptail str).
  Proof. 
    unfold path, Str_nth. intros H n. destruct str. 
    specialize (H (S n)). cbn in *. auto.
  Qed.

  Definition p_global (P : ChainState -> Prop) str := forall n, P (Str_nth n str). 

  Definition pAG (P : ChainState -> Prop) (s : ChainState) : Prop := 
      forall str, path str -> Str_nth 0 str = s -> p_global P str.

  Definition pEG (P : ChainState -> Prop) (s : ChainState) : Prop := 
    exists str, path str /\ Str_nth 0 str = s /\ p_global P str.

  Definition p_finally (P : ChainState -> Prop) str := exists n, P (Str_nth n str).
  
  Definition pAF (P : ChainState -> Prop) (s : ChainState) : Prop := 
    forall str, path str -> Str_nth 0 str = s -> p_finally P str.

  Definition pEF (P : ChainState -> Prop) (s : ChainState) : Prop := 
    exists str, path str /\ Str_nth 0 str = s /\ p_finally P str.

  Definition p_until (P Q : ChainState -> Prop) str := 
    exists n, 
      (forall m, m < n -> P (Str_nth m str)) /\ Q (Str_nth n str).

  Definition pAU (P Q : ChainState -> Prop) (s : ChainState) : Prop := 
    forall str, path str -> Str_nth 0 str = s -> p_until P Q str.

  Definition pEU (P Q : ChainState -> Prop) (s : ChainState) : Prop := 
    exists str, path str /\ Str_nth 0 str = s /\ p_until P Q str.

  (* path semantics *)
  Fixpoint satisfies (addr : Address) (phi : form) (st : ChainState) : Prop :=
    match phi with
    | ctl_propvar P => P addr st
    | ctl_bottom => False
    | ctl_and x y => satisfies addr x st /\ satisfies addr y st
    | ctl_or x y => satisfies addr x st \/ satisfies addr y st
    | ctl_impl x y => satisfies addr x st -> satisfies addr y st     
    | ctl_AX x => cAX (satisfies addr x) st 
    | ctl_EX x => cEX (satisfies addr x) st    
    | ctl_AF x => pAF (satisfies addr x) st
    | ctl_EF x => pEF (satisfies addr x) st
    | ctl_AG x => pAG (satisfies addr x) st
    | ctl_EG x => pEG (satisfies addr x) st
    | ctl_AU x y => pAU (satisfies addr x) (satisfies addr y) st
    | ctl_EU x y => pEU (satisfies addr x) (satisfies addr y) st
    end.
    
End PathSemantics.
End CTL.

Section Agreement.
  Set Nonrecursive Elimination Schemes.
  Context {BaseTypes : ChainBase}.

  (* Parameter State : Type. *)
  (* Parameter Step : State -> State -> Prop. *)

  Lemma trace_cons : forall s s' s'', 
    ChainStep s s' -> ChainTrace s' s'' -> ChainTrace s s''.
  Proof. 
    induction 2. 
    econstructor; eauto using ChainedList. 
    specialize_hypotheses. econstructor; eauto.
  Qed.

  Implicit Type (P : ChainState -> Prop).

  Lemma AGstep {P} : forall s s', ChainStep s s' -> cAG P s -> cAG P s'.
  Proof. destruct 2; auto. Qed.

  Lemma AGmstep {P} : forall s, cAG P s -> forall s' (trace : ChainTrace s s'), cAG P s'.
  Proof. induction 2; eauto using AGstep. Qed.

  Lemma AGnow {P} : forall s, cAG P s -> P s.
  Proof. now destruct 1. Qed.  

  Lemma AG_to_trace {P} : forall s, cAG P s -> forall s' (trace : ChainTrace s s'), P s'.
  Proof. intros. eapply AGnow. eauto using AGmstep. Qed.

  Lemma trace_to_AG {P} : 
    forall s, (forall s' (trace : ChainTrace s s'), P s') -> cAG P s.
  Proof.
    cofix CH.
    intros. apply AGs.
    - apply H. apply clnil.
    - intros. apply CH. intros. apply H. eauto using trace_cons.  
  Qed.

  Lemma safety_to_AG {caddr} phi : 
    (forall s (trace : ChainTrace empty_state s), eval caddr phi s) -> 
    eval caddr (AG phi) empty_state.
  Proof.
    cbn. intros.
    eapply (trace_to_AG); auto. 
  Qed.

  Lemma stream_n_trace : forall st stream n,
    path stream ->
    Str_nth 0 stream = st ->
    inhabited (ChainTrace st (Str_nth n stream)).
  Proof.
    induction n as [|n' IH].
    - intros. subst. repeat constructor.
    - intros. specialize_hypotheses. destruct IH as [trace].
      unfold path in H. specialize (H n') as [step].
      constructor. replace (n' + 1) with (S n') in step by lia.
      exact (snoc trace step).
  Qed.   

  Lemma trace_to_AG_path P :
    (forall bstate, 
      reachable bstate ->
      P bstate) ->
    forall str, path str -> Str_nth 0 str = empty_state -> p_global P str.
  Proof.
    unfold p_global. intros.
    specialize (stream_n_trace empty_state str n) as Htrace. 
    specialize_hypotheses. auto.
  Qed.

  Lemma reachable_state_has_stream {bstate} :
    reachable bstate ->
    exists (str : ChainStream),
      path str /\
      Str_nth 0 str  = bstate.
  Proof.
    intros [trace].
  Abort.

  Fixpoint trace_length {from to} (trace : ChainTrace from to) : nat :=
    match trace with
    | clnil => 0%nat
    | snoc trace' _ => S (trace_length trace')
    end.

  Lemma trace_stream_connect {from to} (stream : ChainStream) 
                             (trace : ChainTrace from to) :
    path stream ->
    Str_nth 0 stream = to ->
    exists (stream' : ChainStream),
      path stream' /\
      Str_nth 0 stream = from /\
      Str_nth (trace_length trace) stream = to.
  Proof.
  Abort.  

  (* Open Scope nat_scope. *)

  Lemma reachable_agreement st :
    reachable st
    <->
    exists str,
      path str /\ Str_nth 0 str = empty_state /\ exists n, Str_nth n str = st. 
  Proof.
    (* split.
    {
      intros reach.
      destruct (reachable_state_has_stream reach) as (stream & Hpath & Hst).
      destruct reach as [trace].
      destruct (trace_stream_connect stream trace) as 
        (stream_total' & ? & ? & ?); eauto.
    }
    {
      intros (pi & Hpath & Hfrom & (n & Hn)).
      unfold path in *.
      generalize dependent st. 
      generalize dependent pi.
      induction n as [|n' IHn'].
      - (* 0 *)
        intros. rewrite Hn in *. subst. 
      - (* ind *) 
        intros.
        specialize (IHn' ltac:(auto) ltac:(auto) ltac:(auto)).
        specialize (IHn' (pi n') ltac:(auto)) as [trace].
        specialize (Hpath n') as (step). 
        replace (S n') with (n' + 1) in Hn by lia.
        rewrite Hn in *.
        constructor. exact (snoc trace step).
    } *)
  Abort. 

  Lemma safety_agreement_ind (P : Address -> ChainState -> Prop) caddr :
    satisfies caddr (AG (ctl P)) empty_state 
    <->
    forall bstate,
      reachable bstate ->
      P caddr bstate.
  Proof.
    (* split.
    {
      cbn. unfold pAG, p_global. intros Hp.
      intros * reach.
      apply (reachable_agreement bstate) in reach as (pi & ? & ? & (n & ?)).
      subst.
      eapply Hp; eauto.
    }
    {
      cbn. unfold pAG, p_global. intros Hp * Hpath Hempty *.
      assert (reach : reachable (pi n)).
      {
        apply (reachable_agreement).
        exists pi. split; auto. split; auto. exists n; auto.
      }
      auto.
    } *)
  Abort.

End Agreement.

Section AFAgreement.
  Context {BaseTypes : ChainBase}.

  Example ex1_AX : forall caddr st,
    eval caddr (AX (ctl (fun addr st' => inhabited (ChainStep st st')))) st.
  Proof.
    intros.
    cbn. unfold cAX. intros; auto.
  Qed.

  Example ex_AF_i : forall caddr st,
    eval caddr (AF (ctl (fun addr st' => inhabited (ChainStep st st')))) st.
  Proof.
    intros. cbn. apply AFs. intros * step. constructor. auto.
  Qed.

  Example ex_AF_p : forall caddr st,
    satisfies caddr (AF (ctl (fun addr st' => inhabited (ChainStep st st')))) st.
  Proof.
    intros. cbn. unfold pAF, p_finally. intros. 
    exists 1.
    unfold path in H. subst. auto.
  Qed.

  Lemma reachable_stream {st} {str} :
    reachable st ->
    path str ->
    Str_nth 0 str = st ->
    forall n, reachable (Str_nth n str).
  Proof.
    induction n.
    rewrite H1; auto.
    unfold path in *. specialize (H0 n) as [step].
    rewrite Nat.add_1_r in *.
    eapply reachable_step; eauto.
  Qed.

  Lemma reachable_through_stream {st} {str} :
    reachable st ->
    path str ->
    Str_nth 0 str = st ->
    forall n, reachable_through st (Str_nth n str).
  Proof.
    induction n.
    rewrite H1; auto.
    unfold path in *. specialize (H0 n) as [step].
    rewrite Nat.add_1_r in *.
    eapply reachable_through_trans; eauto.
  Qed.

  Ltac inversion_subst H := inversion H; subst; clear H.

  Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

  Lemma str_nth_tail str n : 
    Str_nth n (ptail str) = Str_nth (S n) str.
  Proof. destruct str. unfold Str_nth. cbn. auto. Qed.

  Lemma step_action_equiv {prev next1 next2 : ChainState} : 
    ChainStep prev next1 ->
    ChainStep prev next2 ->
    reachable prev ->
    prev.(chain_height) = next1.(chain_height) ->
    prev.(chain_height) = next2.(chain_height) ->
    EnvironmentEquiv next1 next2 /\
    next1.(chain_state_queue) = next2.(chain_state_queue).
  Proof.
    intros * step1 step2 reach Hheight1 Hheight2. 
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
      + (* traceから, queueの矛盾を導く *)
        rewrite_queue.
        destruct (action_trace_step trace) as [|(mid & [step] & [trace'])]; subst.
        * rewrite_environment_equiv. reflexivity.
        * (* contra *)
          assert (reach_at : reachable_in_action_trace next1 next1). apply reachable_in_action_trace_refl; auto. 
          assert (reach_at_mid : reachable_in_action_trace next1 mid). 
          { eapply reachable_in_action_trace_step; eauto. }
          destruct_action_chain_step. rewrite_queue.
          specialize (emited_acts_from_is_always_contract reach_at queue_prev0 eval0) as from_contracts.
          specialize (action_trace_drop_le reach_at_mid trace') as Hle.
          rewrite_queue.
          rewrite no_drop_from_account, drop_until_from_account in Hle; eauto. 
          cbn in *. lia. apply Forall_cons_iff in from_accs as (_ & ?); auto.
      + (* 同様に, traceから, queueの矛盾を導く *)
        rewrite_queue.
        destruct (action_trace_step trace) as [|(mid & [step] & [trace'])]; subst.
        * rewrite_environment_equiv. reflexivity.
        * (* contra *)
          assert (reach_at : reachable_in_action_trace next2 next2). apply reachable_in_action_trace_refl; auto. 
          assert (reach_at_mid : reachable_in_action_trace next2 mid). 
          { eapply reachable_in_action_trace_step; eauto. }
          destruct_action_chain_step. rewrite_queue.
          specialize (emited_acts_from_is_always_contract reach_at queue_prev0 eval0) as from_contracts.
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

  Lemma action_chain_height_eq {from to} :
    ActionChainTrace from to ->
    from.(chain_height) = to.(chain_height).
  Proof.
    remember from. induction 1; subst; auto.
    specialize_hypotheses.
    destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv; auto.
  Qed.

  Local Hint Unfold reachable_in_action_trace : core.

  Lemma go_to_act : forall st act {acts1 acts2} (P : ChainState -> Prop),
    reachable st ->
    st.(chain_state_queue) = acts1 ++ act :: acts2 ->
    P st ->
    (forall (from bstate bstate' : ChainState) act acts new_acts, 
      reachable_in_action_trace from bstate -> 
      P bstate ->
      chain_state_queue bstate = act :: acts -> 
      chain_state_queue bstate' = new_acts ++ acts ->
      (inhabited (ActionEvaluation bstate act bstate' new_acts) 
       \/ EnvironmentEquiv bstate bstate') -> 
      P bstate') ->
    let Pact := fun (bstate : ChainState) =>
      P bstate /\
      bstate.(chain_state_queue) = act :: acts2
    in
    forall str, path str -> Str_nth 0 str = st -> p_finally Pact str.
  Proof.
    unfold p_finally.
    intros * reach queue.
    generalize dependent st.
    induction acts1 as [|act1 acts1' IH]; cbn in *.
    {
      intros. exists 0. split. all:rewrite H2; auto.
    }
    intros * reach queue HP Hpreseved * Hpath Hstart.
    specialize (action_finish_decidable st act1 (acts1' ++ act :: acts2))
     as [(st' & queue' & [action_trace]) |no_finish]; auto.
    - (* finish *)
      assert (preserve : forall bstate, 
        ActionChainTrace st bstate ->
        P bstate  
      ).
      {
        remember st; induction 1; subst; auto.
        destruct_action_chain_step.
        specialize (Hpreseved (Str_nth 0 str) mid to act0 acts new_acts).
        specialize_hypotheses.
        apply Hpreseved; auto.
      }
      assert (inhabited (ChainStep st st')) as [step].
      constructor. eapply (step_action); eauto.
      assert (inhabited (ChainStep st (Str_nth 1 str))) as [step'].
      { unfold path in *. rewrite <- Hstart. auto. }
      destruct (step_action_equiv step step'); auto.
      apply action_chain_height_eq; auto.
      destruct_chain_step; try congruence; try rewrite_environment_equiv; auto.
      apply action_chain_height_eq; auto.
      destruct (IH (Str_nth 1 str)) with (str := ptail str); auto.
      eapply reachable_stream; eauto.
      rewrite_queue; auto.
      destruct_chain_step; try congruence; try rewrite_environment_equiv; auto.
      specialize_hypotheses. rewrite_queue. specialize_hypotheses; auto.
      apply path_ptail; auto.
      rewrite str_nth_tail in *.
      exists (S x). auto. 
    - (* no_finish *)
      specialize (IH (Str_nth 1 str)).
      pose Hpath as Hpath'.
      unfold path in Hpath'. specialize (Hpath' 0) as [step]. cbn in *.
      destruct_chain_step; try congruence.
      + (* contra *)
        destruct (no_finish (Str_nth 1 str)). rewrite Hstart in *. 
        rewrite queue_prev in *. inversion queue. subst. split; auto.
      + (* action_invalid *)
        subst. rewrite queue_prev in *. inversion_subst queue.  
        assert (reachable (Str_nth 1 str)).
        eapply reachable_stream; eauto. 
        specialize_hypotheses.
        assert (P (Str_nth 1 str)).
        eapply  (Hpreseved (Str_nth 0 str) (Str_nth 0 str) (Str_nth 1 str) act1 
          (acts1' ++ act :: acts2) []); eauto. 
        rewrite_queue; auto. 
        right. rewrite_environment_equiv. reflexivity.
        specialize (IH ltac:(auto) ltac:(auto) (ptail str)).
        destruct IH.
        eapply path_ptail; eauto.
        apply str_nth_tail.
        rewrite str_nth_tail in *.
        exists (S x). auto.
  Qed.

  Fixpoint ptails n (str : ChainStream) :=
    match n, str with
    | 0, Cons _ tl => str
    | S n', Cons _ tl => ptails n' tl
    end.

  Lemma str_tl_ptails n str : tl (ptails n str) = ptails n (tl str).
  Proof.
    generalize dependent str. induction n.
    - cbn. destruct str; cbn. destruct str; auto.
    - (* ind *)
      cbn. destruct str; cbn. rewrite IHn. destruct str; cbn. auto.
  Qed.

  Lemma str_nth_tails str n m : 
    Str_nth n (ptails m str) = Str_nth (n + m) str.
  Proof.
    generalize dependent str.
    generalize dependent m. 
    induction n. cbn.
    - induction m. intros. cbn. destruct str; cbn; auto.
      destruct str; cbn. unfold Str_nth in *. cbn in *. auto.
    - (* ind *)
      intros. unfold Str_nth in *. cbn in *.
      rewrite str_tl_ptails. auto.
  Qed.

  Lemma path_ptails n str : path str -> path (ptails n str).
  Proof.
    generalize dependent str. induction n.
    - cbn. destruct str. auto.
    - cbn. destruct str. intros.
      apply IHn.
      replace str with (ptail (Cons c str)). apply path_ptail; auto.
      cbn. auto.
  Qed.

  Lemma AF_intermidiate' {st} {P} :
    let P' := 
      fun st' => forall str, path str -> Str_nth 0 str = st' -> p_finally P str
    in
    (forall str, path str -> Str_nth 0 str = st -> p_finally P' str) ->
    forall str, path str -> Str_nth 0 str = st -> p_finally P str.
  Proof.
    cbn. unfold pAF. intro H.
    unfold p_finally in *. 
    intros. specialize_hypotheses.
    destruct H as (n & H).
    destruct (H (ptails n str)) as (m & ?).
    apply path_ptails; auto.
    apply str_nth_tails.
    exists (m + n). rewrite <- str_nth_tails. auto.
  Qed.

  Lemma AF_intermidiate {caddr} {st} {P} Q :
    satisfies caddr (AF (ctl Q /\' AF (ctl P))) st ->
    satisfies caddr (AF (ctl P)) st.
  Proof.
    cbn. unfold pAF. intro H.
    unfold p_finally in *. 
    intros. specialize_hypotheses.
    destruct H as (n & _ & H).
    destruct (H (ptails n str)) as (m & ?).
    apply path_ptails; auto.
    apply str_nth_tails.
    exists (m + n). rewrite <- str_nth_tails. auto.
  Qed.

  Fixpoint trace_nth (default : ChainState) (n:nat)
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

  Definition path' stream : Prop := forall n, 
    inhabited (ChainStep (Str_nth n stream) (Str_nth (n + 1) stream)).

  Definition p_finally' (P : ChainState -> Prop) stream := 
    exists n, P (Str_nth n stream).

  Definition pAF' (s : ChainState) (P : ChainState -> Prop) : Prop := 
    forall stream, 
      path' stream -> 
        Str_nth 0 stream = s -> 
        p_finally' P stream.

  Lemma stream_trace_equiv : forall {default} from to (trace : ChainTrace from to) stream,
    path' stream ->
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
  Abort.

  Lemma AFs_finally : forall caddr (st to : ChainState) (P : Address -> ChainState -> Prop),
    (
      forall (to' : ChainState),
        EnvironmentEquiv to to' ->
        to.(chain_state_queue) = to'.(chain_state_queue) ->
        P caddr to'
    ) ->
    ChainTrace st to ->
    pAF' st (P caddr).
  Proof.
    unfold pAF', p_finally'.
    intros * H trace * Hpath Hstart.
  Abort.

  Lemma AFs_finally : forall caddr (st to : ChainState) (P : Address -> ChainState -> Prop),
    (
      forall (to' : ChainState),
        EnvironmentEquiv to to' ->
        to.(chain_state_queue) = to'.(chain_state_queue) ->
        P caddr to'
    ) ->
    ChainTrace st to ->
    eval caddr (AF (ctl P)) st.
  Proof.
    intros * H trace.
  Abort.

  Example ex_add_block_height : forall caddr st,
    reachable st ->
    let P := fun addr st' =>
      st'.(chain_state_env).(chain_height) = st'.(chain_state_env).(chain_height) + 1
    in
    eval caddr (AF (ctl P)) st.
  Proof.
    intros * reach. cbn. 
    eapply AFs. intros.
    specialize (empty_queue st (fun _ => True) reach) as Hempty.
    cbn in *.
  Abort.

  Lemma AF2 : forall P st, pAF st P -> cAF st P.
  Proof.
    unfold pAF, p_finally.
    intros.
    eapply AFs.
  Abort.

  (* 
    P が保存するという補題 
    あまりラクになってないかも
    - 前件をChainStepのcaseにする？
  *)
  Lemma preserve : forall st (P : ChainState -> Prop),
    reachable st ->
    P st ->
    (forall (from bstate bstate' : ChainState) act acts new_acts, 
      reachable_in_action_trace from bstate -> 
      P bstate ->
      chain_state_queue bstate = act :: acts -> 
      chain_state_queue bstate' = new_acts ++ acts ->
      (inhabited (ActionEvaluation bstate act bstate' new_acts) 
       \/ EnvironmentEquiv bstate bstate') -> 
      P bstate') ->
    forall st', reachable_through st st' -> P st'.
  (* Proof.
    intros * reach HP Hpreseved * (_ & [trace]).
    
    generalize dependent st.
    induction acts1 as [|act1 acts1' IH]; cbn in *.
    {
      intros. exists 0. split. all:rewrite H2; auto.
    }
    intros * reach queue HP Hpreseved * Hpath Hstart.
    specialize (action_finish_decidable st act1 (acts1' ++ act :: acts2))
     as [(st' & queue' & [action_trace]) |no_finish]; auto.
    - (* finish *)
      assert (preserve : forall bstate, 
        ActionChainTrace st bstate ->
        P bstate  
      ).
      {
        remember st; induction 1; subst; auto.
        destruct_action_chain_step.
        specialize (Hpreseved (Str_nth 0 str) mid to act0 acts new_acts).
        specialize_hypotheses.
        apply Hpreseved; auto.
      }
      assert (inhabited (ChainStep st st')) as [step].
      constructor. eapply (step_action); eauto.
      assert (inhabited (ChainStep st (Str_nth 1 str))) as [step'].
      { unfold path in *. rewrite <- Hstart. auto. }
      destruct (step_action_equiv step step'); auto.
      apply action_chain_height_eq; auto.
      destruct_chain_step; try congruence; try rewrite_environment_equiv; auto.
      apply action_chain_height_eq; auto.
      destruct (IH (Str_nth 1 str)) with (str := ptail str); auto.
      eapply reachable_stream; eauto.
      rewrite_queue; auto.
      destruct_chain_step; try congruence; try rewrite_environment_equiv; auto.
      specialize_hypotheses. rewrite_queue. specialize_hypotheses; auto.
      apply path_ptail; auto.
      rewrite str_nth_tail in *.
      exists (S x). auto. 
    - (* no_finish *)
      specialize (IH (Str_nth 1 str)).
      pose Hpath as Hpath'.
      unfold path in Hpath'. specialize (Hpath' 0) as [step]. cbn in *.
      destruct_chain_step; try congruence.
      + (* contra *)
        destruct (no_finish (Str_nth 1 str)). rewrite Hstart in *. 
        rewrite queue_prev in *. inversion queue. subst. split; auto.
      + (* action_invalid *)
        subst. rewrite queue_prev in *. inversion_subst queue.  
        assert (reachable (Str_nth 1 str)).
        eapply reachable_stream; eauto. 
        specialize_hypotheses.
        assert (P (Str_nth 1 str)).
        eapply  (Hpreseved (Str_nth 0 str) (Str_nth 0 str) (Str_nth 1 str) act1 
          (acts1' ++ act :: acts2) []); eauto. 
        rewrite_queue; auto. 
        right. rewrite_environment_equiv. reflexivity.
        specialize (IH ltac:(auto) ltac:(auto) (ptail str)).
        destruct IH.
        eapply path_ptail; eauto.
        apply str_nth_tail.
        rewrite str_nth_tail in *.
        exists (S x). auto.
  Qed. *)
  Proof. Abort.

End AFAgreement.

Section Merge.

  Context {BaseTypes : ChainBase}.


End Merge.