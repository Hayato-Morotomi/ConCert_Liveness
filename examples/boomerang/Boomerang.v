(** * Boomerang *)

From Coq Require Import ZArith_base.
From Coq Require Import List.
From Coq Require Import Basics.
From Coq Require Import Lia.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.

Import ListNotations.

Open Scope Z.

(** ** Definition *)
Section Boomerang.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

  







  (** The state is the owner's address *)
  Record State :=
    build_state { owner : Address }.

  (** The contract accepts only one message: call by some token *)
  Inductive Msg :=
  | Use (i : Z). 

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition use_boomerang (ctx : ContractCallContext) (st : State) : (State * ActionBody) := 
    ({| owner := st.(owner) |}, act_transfer (ctx.(ctx_from)) (ctx.(ctx_amount))).

  (** The main functionality of the contract.
      Dispatches on a message, validates the input and calls the step functions *)
  Definition boomerang (ctx : ContractCallContext) 
                     (st : State)
                     (msg : Msg)
                     : result (State * list ActionBody) Error := 
    match msg with
    | Use _ =>
      match use_boomerang ctx st with
      | (res_st, act) => Ok (res_st, [act])
      end
    end.  

  (** The "entrypoint" of the contract. Dispatches on a message and calls [boomerang]. *)
  Definition boomerang_receive (chain : Chain)
                             (ctx : ContractCallContext)
                             (state : State)
                             (msg : option Msg)
                             : result (State * list ActionBody) Error :=
    match msg with
    | Some m => match boomerang ctx state m with
                | Ok res => Ok (res)
                | Err e => Err e
                end
    | None => Err default_error
    end.

  (** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
  Definition boomerang_init (chain : Chain)
                          (ctx : ContractCallContext)
                          (init_value : Z)
                          : result State Error :=
    Ok {|
      owner := ctx.(ctx_from)
    |}.

  Section Serialization.
    (** Deriving the [Serializable] instances for the state and for the messages *)
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <Use>. 
      
  End Serialization.

  (** The boomerang contract *)
  Definition boomerang_contract : Contract Z Msg State Error :=
    build_contract boomerang_init boomerang_receive.

End Boomerang.

(** ** Functional properties *)
Section FunctionalProperties.
  Context {BaseTypes : ChainBase}.

  (** *** Specification *)

  (** If the boomerang call succeeds and returns [next_state] then,
       *)
  Lemma boomerang_owner_correct 
    {ctx : ContractCallContext} 
    {prev_state next_state : State} 
    {next_acts : list ActionBody}  
    {msg : Msg} :
    boomerang ctx prev_state msg = Ok (next_state, next_acts) ->
    match msg with
    | Use i => prev_state.(owner) = next_state.(owner)
    end.
  Proof.
    intros H.
    destruct msg. cbn in *. inversion H. simpl. reflexivity.
  Qed.

  Lemma boomerang_acts_correct 
    {ctx : ContractCallContext} 
    {prev_state next_state : State} 
    {next_acts : list ActionBody}  
    {msg : Msg} :
    boomerang ctx prev_state msg = Ok (next_state, next_acts) ->
    exists (to : Address) (amount : Amount), 
      (act_transfer to amount) :: [] = next_acts /\
      ctx.(ctx_from) = to /\
      ctx.(ctx_amount) = amount.
  Proof.
    intros H.
    destruct msg. simpl in H. inversion H.
    exists (ctx_from ctx), (ctx_amount ctx).
    split. reflexivity. split. reflexivity. reflexivity.
  Qed.

End FunctionalProperties.

(** ** Safety properties *)

(** Safety properties are stated for all states reachable from the initial state. *)
Section SafetyProperties.
  Context {BaseTypes : ChainBase}.

  Open Scope program_scope.

  
  Lemma receive_produces_reply_call {chain ctx cstate msg new_cstate} acts :
    boomerang_receive chain ctx cstate msg = Ok (new_cstate, acts) ->
    acts = (act_transfer (ctx_from ctx) (ctx_amount ctx)) :: [].
  Proof.
    intros H.
    destruct msg as [msg |].
    - destruct msg. simpl in H. inversion H. reflexivity.
    - simpl in H. inversion H.
  Qed.

  (* Definition call_amount (adr : Address) (prev_call : ContractCallInfo Msg) : Amount :=
    let amount := prev_call.(call_amount) in
    let from := if (prev_call.(call_from) = adr) then - amount else 0 in
    let origin := if prev_call.(call_origin) = adr then amount else 0 in
    from + origin.

  Definition amount_nextaction (adr : Address) (call_info : list (ContractCallInfo Msg)) : amount :=
    match call_info with
      | [] => 0
      | prev_call :: rest => call_amount adr prev_call
    end. *)

  Definition return_boomerang act_body : Amount :=
    match act_body with
    | act_transfer from amount => amount
    | _                        => 0
    end.

  Definition amount_nextaction (action_list : list ActionBody) : Amount :=
    match action_list with
      | [] => 0
      | act :: rest => return_boomerang act
    end. 

(* Locate env_contracts. *)

  (** We state the following safety property: for all reachable states (i.e. at any point in time after deployment), the state of the counter is equal to the initial value plus the sum of all successful increment and decrement messages sent to the contract.

  We use a special induction principle [contract_induction] that takes care of the boilerplate and exposes the cases in the convenient form. The [tag] variable in the context contains a hint what is expected to be done in each case. *)
  
  Set Ltac Backtrace.

  
  Lemma boomerang_safe block_state boomerang_addr
        (trace : ChainTrace empty_state block_state) :
    env_contracts block_state boomerang_addr = Some (boomerang_contract : WeakContract) ->
    exists (cstate : State) (call_info : list (ContractCallInfo Msg)) (deploy_info : DeploymentInfo Z),
      incoming_calls Msg trace boomerang_addr = Some call_info
      /\ contract_state block_state boomerang_addr = Some cstate
      /\ deployment_info _ trace boomerang_addr = Some deploy_info
      /\ 
      
      let init_amount := deploy_info.(deployment_amount) in
      (* let action_list := block_state.(chain_state_queue) in  *)
      let action_list := outgoing_acts block_state boomerang_addr in
      init_amount =
        (env_account_balances block_state boomerang_addr) - (sumZ act_body_amount action_list).
  Proof.
    contract_induction; intros.
    - (* AddBlock *) 
      apply IH.
    - (* Deploy *)
      simpl. lia. 
    - (* outgoing call *)
      rewrite IH. simpl. lia.
    - (* non recursive *) 
      rewrite IH. 
      simpl in receive_some. 
      apply receive_produces_reply_call in receive_some.
      rewrite receive_some. simpl.
      lia.
    - (* recursive *)
      simpl in receive_some. 
      apply receive_produces_reply_call in receive_some.
      inversion receive_some. 
      simpl. rewrite IH. simpl.
      destruct head.
      + simpl. destruct action_facts as [_ [action_facts _]].
        rewrite action_facts. reflexivity.
      + simpl. lia.
      + simpl. lia.
    - (* Permutaiton *)
      rewrite <- (sumZ_permutation perm). 
      apply IH.
    - (* Facts *)
      instantiate (CallFacts := fun _ _ _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all. subst. 
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.
  
End SafetyProperties.