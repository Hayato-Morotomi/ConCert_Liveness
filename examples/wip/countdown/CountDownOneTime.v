From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Bool.
From ConCert.Utils Require Import Automation Extras.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import ContractCommon.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.

Section CountDownOneTime.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Primitive Projections.

  Context `{BaseTypes : ChainBase}.

  Record Setup := build_setup
    { setup_count : nat }.

  Record State := build_state
  { count : nat;
    ended : bool }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Inductive Msg :=
  | Dec
  | Fin.

  MetaRocq Run (make_setters State).

  (* ---- Serialization (typical in ConCert examples) ---- *)
  Section Serialization.
    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <Dec, Fin>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.
  End Serialization.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup) : result State Error :=
    Ok ({| count := setup.(setup_count);
           ended         := false |}).

  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (st : State)
                     (msg : option Msg)
                     : result (State * list ActionBody) Error :=
    match msg with
    | Some Dec =>
        do _ <- throwIf st.(ended) default_error;
        Ok (st <| count := (st.(count) - 1)%nat |>, [])
    | Some Fin =>
        do _ <- throwIf st.(ended) default_error;
        do _ <- throwIf (0 <? st.(count))%nat default_error;
        Ok (st <| ended := true |>, [])
    | None =>
        Err default_error
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End CountDownOneTime.