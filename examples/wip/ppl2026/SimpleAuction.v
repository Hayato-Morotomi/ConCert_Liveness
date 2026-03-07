(* SimpleAuction.v  (Rocq/ConCert style) *)







(* SPDX-License-Identifier: GPL-3.0 *)
(* pragma solidity ^0.8.4; *)
(* contract SimpleAuction { *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.
From ConCert.Utils Require Import Automation Extras.
From ConCert.Examples.Wip.General Require Import Blockchain_modify.
From ConCert.Examples.Wip.General Require Import ContractCommon_modify.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.

Open Scope Z_scope.

Section SimpleAuction.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Primitive Projections.

  Context `{BaseTypes : ChainBase}.

  Record Setup := build_setup
  { biddingTime : nat;
    beneficiaryAddress : Address }.

  Record State := build_state
  { beneficiary : Address;
    auctionEndTime : nat;
    (* address public highestBidder; *)
    

    highestBidder : option Address;
    highestBid : Amount;
    pendingReturns : AddressMap.AddrMap Amount;
    ended : bool }.

  









  (*
    // Errors that describe failures.
    error AuctionAlreadyEnded();
    error BidNotHighEnough(uint highestBid);
    error AuctionNotYetEnded();
    error AuctionEndAlreadyCalled();
  *)
  Inductive Error :=
  | AuctionAlreadyEnded
  | BidNotHighEnough (highestBid : Amount)
  | AuctionNotYetEnded
  | AuctionEndAlreadyCalled
  
  | NotPayable
  | DefaultError.

  Definition default_error : Error := DefaultError.

  (* Messages that correspond to external calls:
     function bid(), function withdraw(), function auctionEnd() *)
  Inductive Msg :=
  | Bid
  | Withdraw
  | AuctionEnd.

  MetaRocq Run (make_setters State).

  (* ---- Serialization (typical in ConCert examples) ---- *)
  Section Serialization.
    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <Bid, Withdraw, AuctionEnd>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

    Global Instance error_serializable : Serializable Error :=
      Derive Serializable Error_rect <AuctionAlreadyEnded,
                                      BidNotHighEnough,
                                      AuctionNotYetEnded,
                                      AuctionEndAlreadyCalled,
                                      NotPayable,
                                      DefaultError>.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.
  End Serialization.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
    : result State Error :=
    (* constructor is not payable in the given Solidity code *)
    do _ <- throwIf ((ctx.(ctx_amount) >? 0)%Z) NotPayable;
    Ok ({|
      beneficiary   := setup.(beneficiaryAddress);
      auctionEndTime := chain.(chain_height) + setup.(biddingTime);
      highestBidder := None;
      highestBid    := 0%Z;
      pendingReturns := AddressMap.empty;
      ended         := false
    |}).

  (* ---- pendingReturns helpers ---- *)
  Definition get_pendingReturns (a : Address) (m : AddressMap.AddrMap Amount) : Amount :=
    with_default 0 (AddressMap.find a m).

  Definition set_pendingReturns (a : Address) (v : Amount) (m : AddressMap.AddrMap Amount)
    : AddressMap.AddrMap Amount :=
    AddressMap.add a v m.

  Definition add_pendingReturns (a : Address) (delta : Amount) (m : AddressMap.AddrMap Amount)
    : AddressMap.AddrMap Amount :=
    let old := get_pendingReturns a m in
    set_pendingReturns a (old + delta) m.

  (*
    /// Bid on the auction with the value sent
    /// together with this transaction.
    /// The value will only be refunded if the
    /// auction is not won.
    function bid() external payable { ... }
  *)
  Definition bid_step (chain : Chain) (ctx : ContractCallContext) (st : State)
    : result (State * list ActionBody) Error :=
    (*
      // Revert the call if the bidding
      // period is over.
      if (block.timestamp > auctionEndTime)
          revert AuctionAlreadyEnded();
    *)
    do _ <- throwIf (st.(auctionEndTime) <? chain.(chain_height))%nat AuctionAlreadyEnded;
    do _ <- throwIf (ctx.(ctx_amount) <=? st.(highestBid))%Z (BidNotHighEnough st.(highestBid));
    let pendingReturns' :=
      match st.(highestBidder) with
      | None => st.(pendingReturns)
      | Some prev =>
          if (st.(highestBid) =? 0)%Z
          then st.(pendingReturns)
          else add_pendingReturns prev st.(highestBid) st.(pendingReturns)
      end
    in
    Ok (st <| highestBidder := Some ctx.(ctx_from) |> 
           <| pendingReturns := pendingReturns' |>, []).

  








  Definition withdraw_step (chain : Chain) (ctx : ContractCallContext) (st : State)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf ((ctx.(ctx_amount) >? 0)%Z) NotPayable;
    
    match st.(highestBidder) with
    | Some highest_addr =>
        do _ <- throwIf (address_eqb ctx.(ctx_from) highest_addr) default_error; 
        let amount := get_pendingReturns ctx.(ctx_from) st.(pendingReturns) in
        if (0 <? amount)%Z then
          let pendingReturns' := set_pendingReturns ctx.(ctx_from) 0 st.(pendingReturns) in
          Ok (st <| pendingReturns := pendingReturns' |>, [act_transfer ctx.(ctx_from) amount])
        else
          Ok (st, [])
    | None =>
        let amount := get_pendingReturns ctx.(ctx_from) st.(pendingReturns) in
        if (0 <? amount)%Z then
          let pendingReturns' := set_pendingReturns ctx.(ctx_from) 0 st.(pendingReturns) in
          Ok (st <| pendingReturns := pendingReturns' |>, [act_transfer ctx.(ctx_from) amount])
        else
          Ok (st, [])        
    end. 


  (*
    /// End the auction and send the highest bid
    /// to the beneficiary.
    function auctionEnd() external { ... }
  *)
  Definition auction_end_step (chain : Chain) (ctx : ContractCallContext) (st : State)
    : result (State * list ActionBody) Error :=
    (* auctionEnd() is not payable *)
    do _ <- throwIf ((ctx.(ctx_amount) >? 0)%Z) NotPayable;
    do _ <- throwIf (chain.(chain_height) <=? st.(auctionEndTime))%nat AuctionNotYetEnded;
    do _ <- throwIf st.(ended) AuctionEndAlreadyCalled;
    Ok (st <| ended := true |>, [act_transfer st.(beneficiary) st.(highestBid)]).

  (* ---- receive dispatcher ---- *)
  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (st : State)
                     (msg : option Msg)
                     : result (State * list ActionBody) Error :=
    match msg with
    | Some Bid =>
         bid_step chain ctx st
    | Some Withdraw =>
        withdraw_step chain ctx st
    | Some AuctionEnd =>
        auction_end_step chain ctx st
    | None =>
        Err default_error
    end.

  
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End SimpleAuction.