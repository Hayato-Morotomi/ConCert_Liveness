From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Morphisms.
From Stdlib Require Import String.
From Stdlib Require Import Streams.
From Stdlib Require Import Basics.
From Stdlib Require Import Lia.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStream.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import ContractCommon.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepDetermin.
From ConCert.Examples.Wip.ExecutionModel Require Import MyBuildUtils.

Bind Scope Z_scope with Amount.

Section Form.
  Context {BaseTypes : ChainBase}.
  Context {Setup Msg State : Type}.

  Inductive formula :=
    | ltl_atom (P : forall (chain_height : nat)
                    (current_slot : nat)
                    (finalized_height : nat)
                    (caddr : Address)
                    (deployment_info : DeploymentInfo Setup)
                    (cstate : State)
                    (balance : Amount)
                    (outgoing_actions_queued : list ActionBody)
                    (incoming_calls_seen : list (ContractCallInfo Msg))
                    (outgoing_txs_seen : list Tx), Prop)
    | ltl_true
    | ltl_false
    | ltl_not (f : formula)
    | ltl_and (x y : formula)
    | ltl_or (x y : formula)
    | ltl_impl (x y : formula)
    | ltl_G (f : formula)
    | ltl_U (x : formula) (y : formula)

    | ltl_X (f : formula).

  Fixpoint x_free (f : formula) : bool :=
    match f with
    | ltl_atom _ | ltl_true | ltl_false => true
    | ltl_not x | ltl_G x => x_free x
    | ltl_and x y | ltl_or x y | ltl_impl x y | ltl_U x y => x_free x && x_free y
    | ltl_X _ => false
    end.

  Definition Atom : Type :=
    forall (chain_height current_slot finalized_height : nat)
           (caddr : Address)
           (dep_info : DeploymentInfo Setup)
           (cstate : State)
           (balance : Amount)
           (out_acts : list ActionBody)
           (inc_calls : list (ContractCallInfo Msg))
           (out_txs : list Tx), Prop.

End Form.

Notation "'ltl_dep'" :=
  (ltl_not (ltl_atom (fun _ _ _ _ _ _ _ _ _ _ => False)))
  (at level 0).

Section LTL.

  Context {BaseTypes : ChainBase}.

Section PathSemantics.
  Context {Setup Msg State Error : Type}.
  Context `{ser_setup : Serializable Setup}
          `{ser_msg   : Serializable Msg}
          `{ser_state : Serializable State}
          `{ser_error : Serializable Error}.

  Fixpoint satisfies (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (i : nat) (f : formula) : Prop :=
    match f with
    | ltl_atom P =>
      let st := CStr_nth i str in
      let trace := CStr_clist str i in
      env_contracts st caddr = Some (contract : WeakContract) ->
      exists (dep_info : DeploymentInfo Setup)
             (cstate : State)
             (inc_calls : list (ContractCallInfo Msg)),
        deployment_info Setup trace caddr = Some dep_info /\
        contract_state st caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        P st.(chain_height)
          st.(current_slot)
          st.(finalized_height)
          caddr
          dep_info
          cstate
          (env_account_balances st caddr)
          (outgoing_acts st caddr)
          inc_calls
          (outgoing_txs trace caddr)
    | ltl_true => True
    | ltl_false => False
    | ltl_not x => satisfies contract caddr str i x -> False
    | ltl_and x y => satisfies contract caddr str i x /\ satisfies contract caddr str i y
    | ltl_or x y => satisfies contract caddr str i x \/ satisfies contract caddr str i y
    | ltl_impl x y => satisfies contract caddr str i x -> satisfies contract caddr str i y
    | ltl_G x => forall j : nat, (i <= j)%nat -> satisfies contract caddr str j x
    | ltl_U x y => exists j, (i <= j)%nat /\
        (forall k, (i <= k)%nat -> (k < j)%nat ->
          satisfies contract caddr str k x) /\
        satisfies contract caddr str j y
    | ltl_X x => satisfies contract caddr str (S i) x
    end.

  Axiom weakcontract_decidability : forall (wc wc' : WeakContract),
    wc = wc' \/ wc <> wc'.

Section GeneralProperties.

  Lemma deployed_iff_satisfies_ltl_dep
      (contract : Contract Setup Msg State Error)
      (caddr : Address) (str : ChainStream) (i : nat) :
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract) <->
    satisfies contract caddr str i ltl_dep.
  Proof.
    split.
    - intros deployed.
      cbn [satisfies].
      intros Hatom.
      destruct_deployed_typed.
      contradiction.
    - intros Hdep.
      cbn [satisfies] in Hdep.
      destruct (env_contracts (CStr_nth i str) caddr) as [wc|] eqn:deployed.
      + destruct (weakcontract_decidability wc (contract : WeakContract))
          as [wc_eq|wc_ne].
        * subst wc. congruence.
        * exfalso.
          apply Hdep.
          intros deployed_contract.
          exfalso.
          congruence.
      + exfalso.
        apply Hdep.
        intros deployed_contract.
        exfalso.
        congruence.
  Qed.

  Lemma satisfies_ltl_dep_iff
      (contract : Contract Setup Msg State Error)
      (caddr : Address) (str : ChainStream) (i : nat) :
    satisfies contract caddr str i ltl_dep <->
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract).
  Proof.
    destruct (deployed_iff_satisfies_ltl_dep contract caddr str i)
      as [Hdeployed Hsatisfies].
    split; assumption.
  Qed.

  Lemma G_GG_iff (contract : Contract Setup Msg State Error) caddr str i f :
    satisfies contract caddr str i (ltl_G f) <->
    satisfies contract caddr str i (ltl_G (ltl_G f)).
  Proof.
    split; cbn; intros.
    - apply H; lia.
    - eapply H; eauto.
  Qed.

  Lemma satisfies_atom_iff {contract : Contract Setup Msg State Error} (P P' : Atom) caddr str j :
    (forall ch sl fh a dep cs bal out inc txs,
        P ch sl fh a dep cs bal out inc txs <-> P' ch sl fh a dep cs bal out inc txs) ->
    satisfies contract caddr str j (ltl_atom P) <-> satisfies contract caddr str j (ltl_atom P').
  Proof.
    intros Hiff. cbn [satisfies].
    split; intros H Hd; destruct (H Hd) as (d & c & i & H1 & H2 & H3 & HP);
      exists d, c, i; repeat split; auto; apply Hiff; auto.
  Qed.

  Lemma satisfies_G_atom_iff {contract : Contract Setup Msg State Error} (P P' : Atom) caddr str j :
    (forall ch sl fh a dep cs bal out inc txs,
        P ch sl fh a dep cs bal out inc txs <-> P' ch sl fh a dep cs bal out inc txs) ->
    satisfies contract caddr str j (ltl_G (ltl_atom P)) <->
    satisfies contract caddr str j (ltl_G (ltl_atom P')).
  Proof.
    intros Hiff. cbn [satisfies].
    split; intros H k Hjk; specialize (H k Hjk); revert H; apply satisfies_atom_iff;
      intros ch sl fh a dep cs bal out inc txs; specialize (Hiff ch sl fh a dep cs bal out inc txs); tauto.
  Qed.

  Lemma satisfies_atom_intro {contract : Contract Setup Msg State Error}
      caddr str (start : CStr_nth 0 str = empty_state) m (P : Atom) :
    (forall dep cs inc,
        env_contracts (CStr_nth m str) caddr = Some (contract : WeakContract) ->
        deployment_info Setup (CStr_clist str m) caddr = Some dep ->
        contract_state (CStr_nth m str) caddr = Some cs ->
        incoming_calls Msg (CStr_clist str m) caddr = Some inc ->
        P (chain_height (CStr_nth m str)) (current_slot (CStr_nth m str)) (finalized_height (CStr_nth m str))
          caddr dep cs (env_account_balances (CStr_nth m str) caddr) (outgoing_acts (CStr_nth m str) caddr)
          inc (outgoing_txs (CStr_clist str m) caddr)) ->
    satisfies contract caddr str m (ltl_atom P).
  Proof.
    intros HP. cbn [satisfies]. intros Hdep.
    cstr_destruct_deployed_typed.
    exists dep_info, cstate, inc_calls. repeat split; auto.
  Qed.

  Lemma satisfies_atom_elim {contract : Contract Setup Msg State Error}
      caddr str m (P : Atom) dep cs inc :
    satisfies contract caddr str m (ltl_atom P) ->
    env_contracts (CStr_nth m str) caddr = Some (contract : WeakContract) ->
    deployment_info Setup (CStr_clist str m) caddr = Some dep ->
    contract_state (CStr_nth m str) caddr = Some cs ->
    incoming_calls Msg (CStr_clist str m) caddr = Some inc ->
    P (chain_height (CStr_nth m str)) (current_slot (CStr_nth m str)) (finalized_height (CStr_nth m str))
      caddr dep cs (env_account_balances (CStr_nth m str) caddr) (outgoing_acts (CStr_nth m str) caddr)
      inc (outgoing_txs (CStr_clist str m) caddr).
  Proof.
    cbn [satisfies]. intros H Hd H1 H2 H3.
    destruct (H Hd) as (d & c & i & H1' & H2' & H3' & HP). congruence.
  Qed.

End GeneralProperties.

End PathSemantics.

End LTL.

Module LTLNotation.
  Declare Scope ltl_scope.
  Bind Scope ltl_scope with formula.

  Notation "'l_true'"    := ltl_true : ltl_scope.
  Notation "'l_false'"   := ltl_false : ltl_scope.
  Notation "'l_not' x"   := (ltl_not x) (at level 75, right associativity) : ltl_scope.
  Notation "x 'l_and' y"  := (ltl_and x y) (at level 80, right associativity) : ltl_scope.
  Notation "x 'l_or' y"   := (ltl_or x y) (at level 85, right associativity) : ltl_scope.
  Notation "x 'l_impl' y" := (ltl_impl x y) (at level 90, right associativity) : ltl_scope.
  Notation "x 'l_iff' y"  := (ltl_and (ltl_impl x y) (ltl_impl y x)) (at level 95, no associativity) : ltl_scope.

  Notation "'G' x"    := (ltl_G x) (at level 70, right associativity) : ltl_scope.  (* Globally (Always) *)
  Notation "x 'U' y" := (ltl_U x y) (at level 85, right associativity) : ltl_scope. (* Until *)
  Notation "'F' x" := (ltl_U ltl_true x) (at level 70, right associativity) : ltl_scope. (* Finally *)
  Notation "'X' x" := (ltl_X x) (at level 70, right associativity) : ltl_scope.

  Notation "'l_atom' P"  := (ltl_atom P) (at level 70) : ltl_scope.
  Notation "'l_dep'"      := ltl_dep : ltl_scope.
  Notation "'l_undep'"    := (ltl_not ltl_dep) : ltl_scope.
End LTLNotation.
