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

  
  (* Variable contract : Contract Setup Msg State Error. *)

  (* -------------------------------------------- *)
  
  (* -------------------------------------------- *)

Lemma Liveness_rank
    {Setup Msg State Error : Type}
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    {A : Type}
    (R : A -> A -> Prop)
    (wfR : well_founded R)
    (bot : A)
    (eq_decA : forall x y : A, {x = y} + {x <> y})
    (f : Address -> ChainState -> A)
    (P_pre : Address -> ChainState -> Prop)
    (P     : Address -> ChainState -> Prop)
  :
    forall (caddr : Address) (bstate_from : ChainState),
      
      (forall prev next,
          reachable_through bstate_from prev ->
          ChainStep prev next ->
          f caddr prev <> bot ->
          R (f caddr next) (f caddr prev)) ->
      
      (forall st,
          reachable_through bstate_from st ->
          f caddr st = bot ->
          P caddr st) ->
      
      reachable bstate_from ->
      P_pre caddr bstate_from ->
      forall (str : ChainStream),
        path str ->
        Streams.Str_nth 0 str = bstate_from ->
        exists n, P caddr (Streams.Str_nth n str).
  Proof.
    intros * Hdec Hbase _Hreach _Hpre str Hpath Hstart.

    
    set (Q := fun (a : A) =>
      forall i,
        f caddr (Streams.Str_nth i str) = a ->
        exists n, P caddr (Streams.Str_nth (i + n) str)).

    assert (HQ : Q (f caddr bstate_from)).
    {
      (* well-founded induction on rank a *)
      refine (well_founded_induction wfR Q _ _).
      intros a IH i Hfi.
      destruct (eq_decA a bot) as [Habot | Hanot].
      - subst a.
        exists 0.
        replace (i + 0)%nat with i by lia.
        apply Hbase. apply stream_reahchable_through; auto. exact Habot.
      - (* not bot: take one step using path at i *)
        pose Hpath as Hpath'.
        unfold path in Hpath'.
        specialize (Hpath' i) as [step].  (* witness of ChainStep between i and S i *)
        set (st_next := Streams.Str_nth (S i) str).
        set (a_next := f caddr st_next).

        assert (Hprev_not_bot : f caddr (Streams.Str_nth i str) <> bot).
        { rewrite Hfi. exact Hanot. }

        assert (HR : R a_next a).
        { subst a_next. subst a.
          
          eapply Hdec; eauto.
          apply stream_reahchable_through; auto.
          replace (i + 1) with (S i) in step; try lia. subst st_next. auto. }

        (* apply IH on smaller rank at index S i *)
        specialize (IH a_next HR (S i) eq_refl) as [n Hn].
        exists (S n).
        (* i + S n = S i + n *)
        replace (i + S n)%nat with (S i + n)%nat by lia.
        exact Hn.
    }

    
    specialize (HQ 0).
    assert (Hf0 : f caddr (Streams.Str_nth 0 str) = f caddr bstate_from).
    { rewrite Hstart. reflexivity. }
    specialize (HQ Hf0) as [n Hn].
    exists n.
    replace (0 + n)%nat with n in Hn by lia.
    exact Hn.
  Qed.

  (* ------------------------ *)
  
  (* ------------------------ *)

  Lemma Liveness_rank_nat
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      (f : Address -> ChainState -> nat)
      (P_pre : Address -> ChainState -> Prop)
      (P     : Address -> ChainState -> Prop)
    :
    forall (caddr : Address) (bstate_from : ChainState),
      (forall prev next,
          reachable_through bstate_from prev ->
          ChainStep prev next ->
          f caddr prev <> 0 ->
          f caddr next < f caddr prev) ->
      (forall st,
          reachable_through bstate_from st ->
          f caddr st = 0 ->
          P caddr st) ->
      reachable bstate_from ->
      P_pre caddr bstate_from ->
      forall (str : ChainStream),
        path str ->
        Streams.Str_nth 0 str = bstate_from ->
        exists n, P caddr (Streams.Str_nth n str).
  Proof.
    intros Hdec Hbase.
    eapply (Liveness_rank (A:=nat)); eauto.
    apply lt_wf.
    apply Nat.eq_dec.
  Qed.


  
Lemma Liveness_rank_wf_opt
    {Setup Msg State Error : Type}
    `{Serializable Setup}
    `{Serializable Msg}
    `{Serializable State}
    `{Serializable Error}
    {A : Type}
    (R : A -> A -> Prop)
    (wfR : well_founded R)
    (bot : A)
    (eq_decA : forall x y : A, {x = y} + {x <> y})
    (f : Address -> ChainState -> option A)
    (P_pre : Address -> ChainState -> Prop)
    (P     : Address -> ChainState -> Prop)
  :
    forall (caddr : Address) (bstate_from : ChainState),
      
      (P_pre caddr bstate_from -> exists v, f caddr bstate_from = Some v) ->
      
      (forall prev next v1,
          reachable_through bstate_from prev ->
          ChainStep prev next ->
          f caddr prev = Some v1 ->
          v1 <> bot ->
          exists v2,
            f caddr next = Some v2 /\
            R v2 v1) ->
      
      (forall st,
          reachable_through bstate_from st ->
          f caddr st = Some bot ->
          P caddr st) ->
      
      reachable bstate_from ->
      P_pre caddr bstate_from ->
      forall (str : ChainStream),
        path str ->
        Streams.Str_nth 0 str = bstate_from ->
        exists n, P caddr (Streams.Str_nth n str).
Proof.
  intros caddr bstate_from Hdefined Hdec Hbase _Hreach Hpre str Hpath Hstart.

  
  destruct (Hdefined ltac:(auto)) as [v0 Hv0].

  
  set (Q := fun (v : A) =>
    forall i,
      f caddr (Streams.Str_nth i str) = Some v ->
      exists n, P caddr (Streams.Str_nth (i + n) str)).

  assert (HQ : Q v0).
  {
    refine (well_founded_induction wfR Q _ v0).
    intros v IH i Hfi.
    destruct (eq_decA v bot) as [Hvb | Hvb].
    - subst v.
      exists 0%nat.
      replace (i + 0)%nat with i by lia.
      apply Hbase; auto. 
      apply reachable_through_stream; auto.
    - (* v <> bot *)
      assert (reach_prev : reachable_through bstate_from (Str_nth i str)).
      eapply reachable_through_stream; eauto.
      unfold path in Hpath.
      specialize (Hpath i) as [step].
      
      set (st_next := Streams.Str_nth (i + 1) str).
      destruct (Hdec (Streams.Str_nth i str) st_next v reach_prev step Hfi Hvb)
        as [v2 [Hnext HR]].
      specialize (IH v2 HR (i + 1)%nat Hnext) as [n Hn].
      exists (S n).
      replace (i + S n)%nat with ((i + 1) + n)%nat by lia.
      exact Hn.
  }

  
  specialize (HQ 0%nat).
  assert (Hf0 : f caddr (Streams.Str_nth 0 str) = Some v0).
  { rewrite Hstart. exact Hv0. }
  specialize (HQ Hf0) as [n Hn].
  exists n.
  replace (0 + n)%nat with n in Hn by lia.
  exact Hn.
Qed.

  Definition rank_bstate_n n (bstate : ChainState) : (nat * nat) :=
    ((n - bstate.(chain_height))%nat, List.length bstate.(chain_state_queue)).

  
  Definition B (_ : nat) : Type := nat.

  
  Definition R_sig : {x : nat & B x} -> {x : nat & B x} -> Prop :=
    lexprod (A := nat) (B := B) lt (fun _ => lt).

  Lemma wfR_sig : well_founded R_sig.
  Proof.
    apply (wf_lexprod).
    - exact lt_wf.
    - intros. exact lt_wf.
  Qed.

  
  Definition to_sigT (p : nat * nat) : {x : nat & nat} :=
    existT (fst p) (snd p).

  
  Definition R_bstate_n (p q : nat * nat) : Prop :=
    R_sig (to_sigT p) (to_sigT q).

  Lemma wfR_bstate_n : well_founded R_bstate_n.
  Proof.
    unfold R_bstate_n.
    eapply (wf_inverse_image).
    exact wfR_sig.
  Qed.

   
  Lemma eq_dec_prodnat : forall x y : (nat * nat), {x = y} + {x <> y}.
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (Nat.eq_dec x1 y1) as [H1|H1].
    - destruct (Nat.eq_dec x2 y2) as [H2|H2].
      + left. subst. reflexivity.
      + right. intro H. inversion H. congruence.
    - right. intro H. inversion H. congruence.
  Qed.

  Lemma Liveness_rank_bstate
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      (n : nat)
      (P_pre : Address -> ChainState -> Prop)
      (P     : Address -> ChainState -> Prop)
    :
    forall (caddr : Address) (bstate_from : ChainState),
      (forall prev next,
          reachable_through bstate_from prev ->
          ChainStep prev next ->
          rank_bstate_n n prev <> (0, 0) ->
          R_bstate_n (rank_bstate_n n next) (rank_bstate_n n prev)) ->
      (forall st,
          reachable_through bstate_from st ->
          rank_bstate_n n st = (0, 0) ->
          P caddr st) ->
      reachable bstate_from ->
      P_pre caddr bstate_from ->
      forall (str : ChainStream),
        path str ->
        Streams.Str_nth 0 str = bstate_from ->
        exists n, P caddr (Streams.Str_nth n str).
  Proof.
    intros * Hdec Hbase.
    eapply (Liveness_rank) with 
      (R := R_bstate_n) (f:= fun (_ : Address) => rank_bstate_n n); eauto.
    apply wfR_bstate_n. 
    apply eq_dec_prodnat. 
  Qed.


  (* Search "eqb" in Serializable. *)

  Fixpoint interp_type_eqb (t : SerializedType)
    : interp_type t -> interp_type t -> bool :=
    match t with
    | ser_unit => fun _ _ => true
    | ser_int  => fun x y => Z.eqb x y
    | ser_bool => fun x y => Bool.eqb x y
    | ser_pair a b =>
        fun x y =>
          let (x1, x2) := x in
          let (y1, y2) := y in
          andb (interp_type_eqb a x1 y1) (interp_type_eqb b x2 y2)
    | ser_list a =>
        fix list_eqb (xs ys : list (interp_type a)) : bool :=
          match xs, ys with
          | [], [] => true
          | x :: xs', y :: ys' =>
              andb (interp_type_eqb a x y) (list_eqb xs' ys')
          | _, _ => false
          end
    end.

  
  Definition extract_ser_value_eqb (t : SerializedType)
                                (value : SerializedValue)
    : option (interp_type t) :=
    match value with
    | build_ser_value ty val =>
        match SerializedType.eqb_spec t ty with
        | Bool.ReflectT _ Heq =>
            (* Heq : t = ty *)
            match Heq in (_ = ty') return interp_type ty' -> option (interp_type t) with
            | eq_refl => fun v => Some v
            end val
        | Bool.ReflectF _ _ => None
        end
    end.

  Definition SerializedValue_eqb (v1 v2 : SerializedValue) : bool :=
    match v1 with
    | build_ser_value t1 x1 =>
        match extract_ser_value_eqb t1 v2 with
        | Some x2 => interp_type_eqb t1 x1 x2
        | None => false
        end
    end.

  Definition option_SerializedValue_eqb (m1 m2 : option SerializedValue) : bool :=
    match m1, m2 with
    | None, None => true
    | Some x, Some y => SerializedValue_eqb x y
    | _, _ => false
    end.

  
  Record WeakContractEquiv (wc1 wc2 : WeakContract) : Prop :=
    build_wc_equiv {
      init_eq : 
        forall chain ctx setup, wc_init wc1 chain ctx setup = wc_init wc2 chain ctx setup;
      receive_eq :
        forall chain ctx cstate msg, wc_receive wc1 chain ctx cstate msg = wc_receive wc2 chain ctx cstate msg;
    }.

  





  Definition ActionBody_eqb (a b : ActionBody) : bool :=
    match a, b with
    | act_transfer to1 amt1, act_transfer to2 amt2 =>
        (address_eqb to1 to2) && Z.eqb amt1 amt2
    | act_call to1 amt1 msg1, act_call to2 amt2 msg2 =>
        (address_eqb to1 to2) && Z.eqb amt1 amt2 && SerializedValue_eqb msg1 msg2
    | act_deploy amt1 c1 setup1, act_deploy amt2 c2 setup2 => 
        Z.eqb amt1 amt2 && SerializedValue_eqb setup1 setup2
    | _, _ => false
    end.  

  Definition act_eqb (a b : Action) : bool :=
    Nat.eqb (act_limit a) (act_limit b)
    && (address_eqb (act_origin a) (act_origin b))
    && (address_eqb (act_from a) (act_from b))
    && ActionBody_eqb (act_body a) (act_body b).

  
  Fixpoint length_until_act' (res : nat) (a : Action) l : option nat :=
      match l with
      | [] => None
      | h :: tl => if act_eqb a h then 
          Some res
        else length_until_act' (res + 1) a tl
      end.

  Definition length_until_act := length_until_act' 0.

  
  Lemma Liveness_fairness
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      (acts : list Action)
      (P_pre : Address -> ChainState -> Prop)
      (P     : Address -> ChainState -> Prop)
    :
      forall (caddr : Address) (bstate_from : ChainState),
        (forall prev next,
          reachable_through bstate_from prev ->
          ChainStep prev next ->
          prev.(chain_state_queue) = [] -> 
          Forall (fun act => In act next.(chain_state_queue)) acts) ->
        P_pre caddr bstate_from ->
        forall (str : ChainStream),
          path str ->
          Streams.Str_nth 0 str = bstate_from ->
          exists n, P caddr (Streams.Str_nth n str).
  Proof.
  Abort.

  Lemma Liveness_rank_wf'
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      {A : Type}
      (R : A -> A -> Prop)
      (wfR : well_founded R)
      (bot : A)
      (eq_decA : forall x y : A, {x = y} + {x <> y})
      (f : Address -> ChainState -> A)
      (P_pre : Address -> ChainState -> Prop)
      (P     : Address -> ChainState -> Prop)
    :
      
      (forall caddr prev next,
          ChainStep prev next ->
          (* f caddr prev <> bot -> *)
          R bot (f caddr prev) -> 
          R (f caddr next) (f caddr prev)) ->
      
      (forall caddr st,
          f caddr st = bot ->
          P caddr st) ->
      forall (caddr : Address) (bstate_from : ChainState),
        reachable bstate_from ->
        P_pre caddr bstate_from ->
        forall (str : ChainStream),
          path str ->
          Streams.Str_nth 0 str = bstate_from ->
          exists n, P caddr (Streams.Str_nth n str).
  





















































  Abort.

  
  Lemma Liveness_rank_wf_opt_strong
      {Setup Msg State Error : Type}
      `{Serializable Setup}
      `{Serializable Msg}
      `{Serializable State}
      `{Serializable Error}
      {A : Type}
      (R : A -> A -> Prop)
      (wfR : well_founded R)
      (bot : A)
      (eq_decA : forall x y : A, {x = y} + {x <> y})
      (f : Address -> ChainState -> option A)
      (P_pre : Address -> ChainState -> Prop)
      (P     : Address -> ChainState -> Prop)
    :
      forall (caddr : Address) (bstate_from : ChainState),
        (* start_some *)
        (P_pre caddr bstate_from -> exists v, f caddr bstate_from = Some v) ->
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
        (* bottom *)
        (forall st,
            reachable_through bstate_from st ->
            f caddr st = Some bot ->
            P caddr st) ->
        (* statement *)
        reachable bstate_from ->
        P_pre caddr bstate_from ->
        forall (str : ChainStream),
          path str ->
          Str_nth 0 str = bstate_from ->
          exists n, P caddr (Str_nth n str).
  Proof.
    intros caddr bstate_from Hdefined Hevdec Hbot Hreach Hpre str Hpath Hstart.

    destruct (Hdefined Hpre) as [v0 Hv0].

    
    set (Q := fun (v : A) =>
      forall i,
        f caddr (Str_nth i str) = Some v ->
        exists n, P caddr (Str_nth (i + n) str)).

    assert (HQ0 : Q v0).
    {
      refine (well_founded_induction wfR (fun v => Q v) _ _).
      intros v IH i Hfi.
      destruct (eq_decA v bot) as [Hvb | Hvb].
      - subst v.
        exists 0%nat.
        replace (i + 0)%nat with i by lia.
        apply (Hbot (Str_nth i str)).
        + (* reachable_through *)
          
          eapply reachable_through_stream; eauto.
        + exact Hfi.
      - 
        pose (sti := Str_nth i str).
        assert (Hreach_i : reachable_through bstate_from sti).
        { subst sti. eapply reachable_through_stream; eauto. }
        set (str_i := Str_nth_tl i str).
        assert (H0_i : Str_nth 0 str_i = sti).
        { subst str_i sti. rewrite Str_nth_plus. reflexivity. }
      

        


        assert (Hpath_i : path str_i).
        { unfold str_i. apply stream_path_nth_tl; auto. }
        destruct (Hevdec sti v Hreach_i Hfi Hvb str_i H0_i Hpath_i)
          as [j [v2 [Hfj HR]]].

        
        assert (Hf_ij : f caddr (Str_nth (i + j) str) = Some v2).
        { subst str_i. rewrite Str_nth_plus, Nat.add_comm in Hfj. auto. }

        destruct (IH v2 HR (i + j)%nat Hf_ij) as [n Hn].
        exists (j + n)%nat.
        replace (i + (j + n))%nat with ((i + j) + n)%nat by lia.
        exact Hn.
    }
    specialize (HQ0 0%nat).
    assert (Hf0 : f caddr (Str_nth 0 str) = Some v0) by (rewrite Hstart; exact Hv0).
    destruct (HQ0 Hf0) as [n Hn].
    exists n.
    replace (0 + n)%nat with n in Hn by lia. auto.
  Qed.

  
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

  Local Open Scope Z.

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


Section Liveness.
  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

  Lemma Liveness
      {Setup Msg State Error : Type}
     `{Serializable Setup}
     `{Serializable Msg}
     `{Serializable State}
     `{Serializable Error}
    (contract : Contract Setup Msg State Error) 
    (P_pre : forall bstate caddr, Prop)                      
    (P : forall bstate_mid caddr, Prop) 
    (f : Address -> ChainState -> nat) (* ranking function *)
                                                        :
    forall (caddr : Address) (bstate_from : ChainState), 
      (* ranking *)
      (
        forall prev next, 
          ChainStep prev next ->
          f caddr prev < f caddr next
      ) ->
      (* finally *)
      (
        forall st,
          f caddr st = 0 
          -> P st caddr 
      ) ->

      (* liveness *)
      reachable bstate_from -> 
      P_pre bstate_from caddr ->
      forall str, path str -> Str_nth 0 str = bstate_from -> exists n, P (Str_nth n str) caddr.
  Proof.
    intros caddr bstate.
    remember (f caddr bstate) as n.
    generalize dependent bstate.
    induction n. 
    - (* n = 0 *)
      intros.
      exists 0. subst bstate. apply H4; auto.
    - (* ind *)
      intros.
      remember empty_state; destruct [H5]; subst.
  Abort.
End Liveness.