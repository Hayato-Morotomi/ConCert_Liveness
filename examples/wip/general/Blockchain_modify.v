











(** This file defines blockchains, both a contract's view (which is
more computational) and the semantics of executing smart contracts
in a blockchain.

The most important types are:

- The [ChainBase] type describes basic assumptions made of any blockchain.
  In most cases, we will abstract over this type.

- The [Chain] type describes a smart contract's view of the blockchain.
  This is the data that can be accessed by smart contracts.

- The [Action] type describes how smart contracts (and external users)
  interact with the blockchain. We allow transfers, calls and deployment
  of contracts.

- The [WeakContract] type describes a "weak" or "stringly" typed
  version of smart contracts. Contracts are just two functions init and
  receive to respectively initialize the state on deployment and update
  the state when receiving messages. The weak version of contracts means that
  the state/message/setup types, which would normally vary with contracts,
  are stored in a serialized format.

- The [Contract] type describes a more strongly typed version of a contract.
  This is the same as the above except we abstract over the appropriate types.
  Users of the framework will mostly need to deal with this.

The next types deal with semantics.

- The [Environment] type augments the Chain type with more information.
  [Environment] can be thought of as the information that a realistic blockchain
  implementation would need to keep track of to implement operations. For instance,
  it is reasonable to assume that an implementation needs to access the state of
  contracts, but not to assume that it needs to store the full transaction history
  of all addresses.

- The [ActionEvaluation] type. This specifies how to evaluate actions returned by
  contracts or input in blocks. This related an environment and action to a new
  environment and a list of new actions to execute.

- The [ChainState] type. This augments the [Environment] type with a queue of
  "outstanding" actions that need to be executed. For instance, when a block is
  added, its actions are put into this queue.

- The [ChainStep] type. This specifies how the blockchain should execute smart
  contracts, and how new blocks are added. It relates a [ChainState] to a new [ChainState].
  There are steps to allow adding blocks, evaluating actions in the queue and permuting
  the queue (allowing to model any execution order).

- The [ChainTrace] type. This just represents a sequence of steps. If a trace ends
  in a state it means that the state is [reachable] and there is a "semantically correct"
  way of executing to get to this state. This type records the full history of a
  blockchain's execution, and it would thus be unrealistic to extract.

- The [ChainBuilderType] type. This is a typeclass for implementations of blockchains,
  where these implementations need to prove that they satisfy our semantics.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
From Stdlib Require Import Permutation.
From Stdlib Require Import Morphisms.
From Stdlib Require Import String.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.

Definition Amount := Z.
Bind Scope Z_scope with Amount.

Class ChainBase :=
  build_chain_base {
    Address : Type;
    address_eqb : Address -> Address -> bool;
    address_eqb_spec :
      forall (a b : Address), Bool.reflect (a = b) (address_eqb a b);
    address_eqdec :: stdpp.base.EqDecision Address;
    address_countable :: countable.Countable Address;
    address_serializable :: Serializable Address;
    address_is_contract : Address -> bool;
  }.

Global Opaque Address address_eqb address_eqb_spec
              address_eqdec address_countable
              address_serializable.

Declare Scope address_scope.
Delimit Scope address_scope with address.
Bind Scope address_scope with Address.
Infix "=?" := address_eqb (at level 70) : address_scope.

Definition address_neqb `{ChainBase} (x y : Address) : bool :=
  negb (address_eqb x y).

Definition address_not_contract `{ChainBase} (x : Address) : bool :=
  negb (address_is_contract x).

Lemma address_eq_refl `{ChainBase} x :
  address_eqb x x = true.
Proof. destruct (address_eqb_spec x x); auto; congruence. Qed.

Lemma address_eq_ne `{ChainBase} x y :
  x <> y ->
  address_eqb x y = false.
Proof.
  destruct (address_eqb_spec x y) as [->|]; tauto.
Qed.

Lemma address_eq_ne' `{ChainBase} x y :
  x <> y <->
  address_eqb x y = false.
Proof.
  split; destruct (address_eqb_spec x y) as [->|]; (discriminate || tauto).
Qed.

Lemma address_eq_sym `{ChainBase} x y :
  address_eqb x y = address_eqb y x.
Proof.
  destruct (address_eqb_spec x y) as [->|].
  - now rewrite address_eq_refl.
  - rewrite address_eq_ne; auto.
Qed.

Lemma address_neqb_eq `{ChainBase} x y :
  address_neqb x y = false <->
  x = y.
Proof.
  unfold address_neqb.
  rewrite Bool.negb_false_iff.
  now destruct (address_eqb_spec x y).
Qed.

Lemma address_neq_sym `{ChainBase} x y :
  address_neqb x y = address_neqb y x.
Proof.
  unfold address_neqb.
  f_equal.
  apply address_eq_sym.
Qed.

Global Ltac destruct_address_eq :=
  repeat
    match goal with
    | [H: context[address_eqb ?a ?b] |- _] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [|- context[address_eqb ?a ?b]] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [H: context[address_neqb ?a ?b] |- _] =>
      try unfold address_neqb in *; destruct (address_eqb_spec a b)
    | [|- context[address_neqb ?a ?b]] =>
      try unfold address_neqb in *; destruct (address_eqb_spec a b)
    end.

Section Blockchain.
  Context {Base : ChainBase}.

  (** This represents the view of the blockchain that a contract
  can access and interact with. *)
  Record Chain :=
    build_chain {
      chain_height : nat;
      current_slot : nat;
      finalized_height : nat;
    }.

  Record ContractCallContext :=
    build_ctx {
      (** **)
      ctx_limit : nat;
      (** Address that initiated the transaction (never a contract) *)
      ctx_origin : Address;
      (** Address of the immediate account that sent
          the call (can be a contract or a user account) *)
      ctx_from : Address;
      (** Address of the contract being called *)
      ctx_contract_address : Address;
      (** Balance of the contract being called *)
      ctx_contract_balance : Amount;
      (** Amount of currency passed in call *)
      ctx_amount : Amount;
    }.

  MetaRocq Run (make_setters ContractCallContext). 

  (** Operations that a contract can return or that a user can use
  to interact with a chain. *)
  Inductive ActionBody :=
  | act_transfer (to : Address) (amount : Amount)
  | act_call (to : Address) (amount : Amount) (msg : SerializedValue)
  | act_deploy (amount : Amount) (c : WeakContract) (setup : SerializedValue)
  with WeakContract :=
      | build_weak_contract
          (init :
              Chain ->
              ContractCallContext ->
              SerializedValue (* setup *) ->
              result SerializedValue SerializedValue)
          (receive :
              Chain ->
              ContractCallContext ->
              SerializedValue (* state *) ->
              option SerializedValue (* message *) ->
              result (SerializedValue * list ActionBody) SerializedValue).

  Definition act_body_amount (ab : ActionBody) : Z :=
    match ab with
    | act_transfer _ amount
    | act_call _ amount _
    | act_deploy amount _ _ => amount
    end.

  Definition wc_init (wc : WeakContract) :=
    let (i, _) := wc in i.

  Definition wc_receive (wc : WeakContract) :=
    let (_, r) := wc in r.

  Record Action :=
    build_act {
      act_limit : nat;
      act_origin : Address;
      act_from : Address;
      act_body : ActionBody;
    }.

  Definition act_amount (a : Action) :=
    act_body_amount (act_body a).

  (** Represents a strongly-typed contract. This is what users will primarily
  use and interact with when they want deployment. We keep the weak contract
  only "internally" for blockchains, while any strongly-typed contract can
  be converted to and from *)
  Record Contract
        (Setup Msg State Error : Type)
        `{Serializable Setup}
        `{Serializable Msg}
        `{Serializable State}
        `{Serializable Error} :=
    build_contract {

      init :
        Chain ->
        ContractCallContext ->
        Setup ->
        result State Error;

      receive :
        Chain ->
        ContractCallContext ->
        State ->
        option Msg ->
        result (State * list ActionBody) Error;
    }.

  Global Arguments init {_ _ _ _ _ _ _ _}.
  Global Arguments receive {_ _ _ _ _ _ _ _}.
  Global Arguments build_contract {_ _ _ _ _ _ _ _}.

  Definition deser_error :=
    serialize "Deserialization failed"%string.
  Definition error_to_weak_error {T E : Type}
                                `{Serializable E}
                                (r : result T E)
                                : result T SerializedValue :=
    bind_error (fun err => serialize err) r.

  Definition contract_to_weak_contract
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            (c : Contract Setup Msg State Error)
            : WeakContract :=
        let weak_init chain ctx ser_setup :=
            do setup <- result_of_option (deserialize ser_setup) deser_error;
            do state <- error_to_weak_error (c.(init) chain ctx setup);
            Ok (serialize state) in
        let weak_recv chain ctx ser_state ser_msg_opt :=
            do state <- result_of_option (deserialize ser_state) deser_error;
            match ser_msg_opt with
            | Some ser_msg =>
              do msg <- result_of_option (deserialize ser_msg) deser_error;
              do '(new_state, acts) <- error_to_weak_error (c.(receive) chain ctx state (Some msg));
              Ok (serialize new_state, acts)
            | None =>
              do '(new_state, acts) <- error_to_weak_error (c.(receive) chain ctx state None);
              Ok (serialize new_state, acts)
            end in
        build_weak_contract weak_init weak_recv.

  Coercion contract_to_weak_contract : Contract >-> WeakContract.

  (** Deploy a strongly typed contract with some amount and setup *)
  Definition create_deployment
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            (amount : Amount)
            (contract : Contract Setup Msg State Error)
            (setup : Setup) : ActionBody :=
    act_deploy amount contract (serialize setup).

  (** The contract interface is the main mechanism allowing a deployed
  contract to interact with another deployed contract. This hides
  the ugly details of everything being SerializedValue away from contracts. *)
  Record ContractInterface {Msg : Type} :=
    build_contract_interface {
      (** The address of the contract being interfaced with *)
      contract_address : Address;
      (** Make an action sending money and optionally a message to the contract *)
      send : Amount -> option Msg -> ActionBody;
    }.

  Global Arguments ContractInterface _ : clear implicits.

  Definition get_contract_interface
            (chain : Chain)
            (addr : Address)
            (Msg : Type)
            `{Serializable Msg}
            : option (ContractInterface Msg) :=
    let ifc_send amount msg :=
        match msg with
        | None => act_transfer addr amount
        | Some msg => act_call addr amount (serialize msg)
        end in
    Some {| contract_address := addr; send := ifc_send; |}.

Section Semantics.
  MetaRocq Run (make_setters Chain).

  Definition add_balance
            (addr : Address)
            (amount : Amount)
            (map : Address -> Amount)
            : Address -> Amount :=
    fun a => if (a =? addr)%address
            then (amount + map a)%Z
            else map a.

  Global Arguments add_balance _ _ _ /.

  Definition set_chain_contract_state
            (addr : Address)
            (state : SerializedValue)
            (map : Address -> option SerializedValue)
            : Address -> option SerializedValue :=
    fun a => if (a =? addr)%address
            then Some state
            else map a.

  Record Environment :=
    build_env {
      env_chain :> Chain;
      env_account_balances : Address -> Amount;
      env_contracts : Address -> option WeakContract;
      env_contract_states : Address -> option SerializedValue;
    }.

  (** Two environments are equivalent if they are extensionally equal *)
  Record EnvironmentEquiv (e1 e2 : Environment) : Prop :=
    build_env_equiv {
      chain_eq : env_chain e1 = env_chain e2;
      account_balances_eq :
        forall a, env_account_balances e1 a = env_account_balances e2 a;
      contracts_eq :
        forall a, env_contracts e1 a = env_contracts e2 a;
      contract_states_eq :
        forall addr, env_contract_states e1 addr = env_contract_states e2 addr;
    }.

  (** Strongly typed version of the contract state *)
  Definition contract_state
            {A : Type}
            `{Serializable A}
            (env : Environment)
            (addr : Address)
            : option A :=
    env_contract_states env addr >>= deserialize.

  Global Program Instance environment_equiv_equivalence : Equivalence EnvironmentEquiv.
  Next Obligation.
    apply build_env_equiv; reflexivity.
  Qed.
  Next Obligation.
    destruct H; apply build_env_equiv; now symmetry.
  Qed.
  Next Obligation.
    destruct H, H0; apply build_env_equiv; try congruence.
  Qed.

  Global Instance environment_equiv_env_account_balances_proper :
    Proper (EnvironmentEquiv ==> eq ==> eq) env_account_balances.
  Proof. repeat intro; subst; apply account_balances_eq; assumption. Qed.

  Global Instance environment_equiv_env_contracts_proper :
    Proper (EnvironmentEquiv ==> eq ==> eq) env_contracts.
  Proof. repeat intro; subst; apply contracts_eq; assumption. Qed.

  Global Instance environment_equiv_env_contract_states_proper :
    Proper (EnvironmentEquiv ==> eq ==> eq) env_contract_states.
  Proof. repeat intro; subst; apply contract_states_eq; assumption. Qed.

  Global Instance environment_equiv_env_chain_equiv_proper :
    Proper (EnvironmentEquiv ==> eq) env_chain.
  Proof. repeat intro; apply chain_eq; assumption. Qed.

  Global Instance environment_equiv_contract_state_proper
    {A : Type} `{Serializable A} :
    Proper (EnvironmentEquiv ==> eq ==> (@eq (option A))) contract_state.
  Proof.
    intros ? ? env_eq ? ? ?.
    subst.
    unfold contract_state.
    now rewrite env_eq.
  Qed.

  MetaRocq Run (make_setters Environment).

  Definition transfer_balance (from to : Address) (amount : Amount) (env : Environment) :=
    env<|env_account_balances ::= add_balance to amount|>
      <|env_account_balances ::= add_balance from (-amount)|>.

  Definition add_contract (addr : Address) (contract : WeakContract) (env : Environment)
    : Environment :=
    env<|env_contracts ::=
      fun f a =>
        if (a =? addr)%address
        then Some contract
        else f a|>.

  Definition set_contract_state
            (addr : Address) (state : SerializedValue) (env : Environment) :=
    env<|env_contract_states ::= set_chain_contract_state addr state|>.

  (* set_chain_contract_state updates a map (function) by returning a
    new map (function). If this function is immediately applied to a
    key, then unfold it. *)
  Global Arguments set_chain_contract_state _ _ _ /.

  Ltac rewrite_environment_equiv :=
    match goal with
    | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
    end.

  Ltac solve_proper :=
    apply build_env_equiv;
    cbn;
    repeat intro;
    repeat rewrite_environment_equiv;
    auto.

  Global Instance transfer_balance_proper :
    Proper (eq ==> eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) transfer_balance.
  Proof.
    repeat intro; subst.
    unfold transfer_balance, add_balance.
    solve_proper.
  Qed.

  Global Instance add_contract_proper :
    Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) add_contract.
  Proof.
    repeat intro; subst.
    unfold add_contract.
    solve_proper.
  Qed.

  Global Instance set_contract_state_proper :
    Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) set_contract_state.
  Proof.
    repeat intro; subst.
    unfold set_contract_state, set_chain_contract_state.
    solve_proper.
  Qed.

  Local Open Scope Z.
  (* Next we define how actions are executed. It specifies how an action
  changes an environment and which external actions to execute after it.
  Note that there can be multiple ways to execute an action. For example, if
  the action says to deploy a contract, the implementation is responsible for
  selecting which address the new contract should get. *)
  Inductive ActionEvaluation
            (prev_env : Environment) (act : Action)
            (new_env : Environment) (new_acts : list Action) : Type :=
    | eval_transfer :
        forall (limit : nat)
               (origin from_addr to_addr : Address)
               (amount : Amount),
          (limit > 0)%nat -> 
          amount >= 0 ->
          amount <= env_account_balances prev_env from_addr ->
          address_is_contract to_addr = false ->
          act = build_act limit origin from_addr (act_transfer to_addr amount) ->
          EnvironmentEquiv
            new_env
            (transfer_balance from_addr to_addr amount prev_env) ->
          new_acts = [] ->
          ActionEvaluation prev_env act new_env new_acts
    | eval_deploy :
        forall (limit : nat) 
               (origin from_addr to_addr : Address)
               (amount : Amount)
               (wc : WeakContract)
               (setup : SerializedValue)
               (state : SerializedValue),
        (limit > 0)%nat ->
        amount >= 0 ->
        amount <= env_account_balances prev_env from_addr ->
        address_is_contract to_addr = true ->
        env_contracts prev_env to_addr = None ->
        act = build_act limit origin from_addr (act_deploy amount wc setup) ->
        wc_init
          wc 
          (transfer_balance from_addr to_addr amount prev_env) 
          (build_ctx limit origin from_addr to_addr amount amount)
          setup = Ok state ->
        EnvironmentEquiv
          new_env
          (set_contract_state
            to_addr state (add_contract
                        to_addr wc (transfer_balance from_addr to_addr amount prev_env))) ->
        new_acts = [] ->
        ActionEvaluation prev_env act new_env new_acts
    | eval_call :
        forall (limit : nat) 
              (origin from_addr to_addr : Address)
              (amount : Amount)
              (wc : WeakContract)
              (msg : option SerializedValue)
              (prev_state : SerializedValue)
              (new_state : SerializedValue)
              (resp_acts : list ActionBody),
        (limit > 0)%nat ->
        amount >= 0 ->
        amount <= env_account_balances prev_env from_addr ->
        env_contracts prev_env to_addr = Some wc ->
        env_contract_states prev_env to_addr = Some prev_state ->
        act = build_act limit origin from_addr
                        (match msg with
                        | None => act_transfer to_addr amount
                        | Some msg => act_call to_addr amount msg
                        end) ->
        wc_receive
          wc
          (transfer_balance from_addr to_addr amount prev_env)
          (build_ctx limit origin from_addr to_addr (env_account_balances new_env to_addr) amount)
          prev_state
          msg = Ok (new_state, resp_acts) ->
        new_acts = map (build_act (limit - 1)%nat origin to_addr) resp_acts ->
        EnvironmentEquiv
          new_env
          (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev_env)) ->
        ActionEvaluation prev_env act new_env new_acts.

  Global Arguments eval_transfer {_ _ _ _ }.
  Global Arguments eval_deploy {_ _ _ _ }.
  Global Arguments eval_call {_ _ _ _}.

Section Accessors.
  Context {origin : Address}
          {pre : Environment} {act : Action}
          {post : Environment} {new_acts : list Action}
          (eval : ActionEvaluation pre act post new_acts).

  Definition eval_limit : nat :=
    match eval with
    | eval_transfer limit _ _ _ _ _ _ _ _ _ _ _
    | eval_deploy limit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | eval_call limit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => limit
    end.    

  Definition eval_origin : Address :=
    match eval with
    | eval_transfer _ origin _ _ _ _ _ _ _ _ _ _
    | eval_deploy _ origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | eval_call _ origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => origin
    end.

  Definition eval_from : Address :=
    match eval with
    | eval_transfer _ _ from _ _ _ _ _ _ _ _ _
    | eval_deploy _ _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | eval_call _ _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
    end.

  Definition eval_to : Address :=
    match eval with
    | eval_transfer _ _ _ to _ _ _ _ _ _ _ _
    | eval_deploy _ _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _
    | eval_call _ _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => to
    end.

  Definition eval_amount : Amount :=
    match eval with
    | eval_transfer _ _ _ _ amount _ _ _ _ _ _ _
    | eval_deploy _ _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _
    | eval_call _ _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ => amount
    end.
End Accessors.

Section Theories.
  Context {origin : Address}
          {pre : Environment} {act : Action}
          {post : Environment} {new_acts : list Action}
          (eval : ActionEvaluation pre act post new_acts).

  Lemma account_balance_post (addr : Address) :
    env_account_balances post addr =
    env_account_balances pre addr
    + (if (addr =? eval_to eval)%address then eval_amount eval else 0)
    - (if (addr =? eval_from eval)%address then eval_amount eval else 0).
  Proof.
    destruct eval; cbn; rewrite_environment_equiv; cbn;
      destruct_address_eq; lia.
  Qed.

  Lemma account_balance_post_to :
    eval_from eval <> eval_to eval ->
    env_account_balances post (eval_to eval) =
    env_account_balances pre (eval_to eval) + eval_amount eval.
  Proof.
    intros neq.
    rewrite account_balance_post.
    rewrite address_eq_refl, address_eq_ne by auto.
    lia.
  Qed.

  Lemma account_balance_post_from :
    eval_from eval <> eval_to eval ->
    env_account_balances post (eval_from eval) =
    env_account_balances pre (eval_from eval) - eval_amount eval.
  Proof.
    intros neq.
    rewrite account_balance_post.
    rewrite address_eq_refl, address_eq_ne by auto.
    lia.
  Qed.

  Lemma account_balance_post_irrelevant (addr : Address) :
    addr <> eval_from eval ->
    addr <> eval_to eval ->
    env_account_balances post addr = env_account_balances pre addr.
  Proof.
    intros neq_from neq_to.
    rewrite account_balance_post.
    repeat rewrite address_eq_ne by auto.
    lia.
  Qed.

  Lemma chain_height_post_action : chain_height post = chain_height pre.
  Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

  Lemma current_slot_post_action : current_slot post = current_slot pre.
  Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

  Lemma finalized_height_post_action : finalized_height post = finalized_height pre.
  Proof. destruct eval; rewrite_environment_equiv; auto. Qed.

  Lemma contracts_post_pre_none contract :
    env_contracts post contract = None ->
    env_contracts pre contract = None.
  Proof.
    intros H.
    destruct eval; rewrite_environment_equiv; auto.
    cbn in *.
    destruct_address_eq; congruence.
  Qed.

  Lemma eval_amount_nonnegative : eval_amount eval >= 0.
  Proof. now destruct eval. Qed.

  Lemma eval_amount_le_account_balance :
    eval_amount eval <= env_account_balances pre (eval_from eval).
  Proof. now destruct eval. Qed.

End Theories.

Section Trace.

  Record BlockHeader :=
    build_block_Header {
      block_height : nat;
      block_slot : nat;
      block_finalized_height : nat;
      block_reward : Amount;
      block_creator : Address;
    }.

  Definition add_new_block_to_env
            (header : BlockHeader) (env : Environment) : Environment :=
    env<|env_chain; chain_height := block_height header|>
      <|env_chain; current_slot := block_slot header|>
      <|env_chain; finalized_height := block_finalized_height header|>
      <|env_account_balances ::=
          add_balance (block_creator header) (block_reward header)|>.

  (* Todo: this should just be a computation. But I still do not *)
  (* know exactly what the best way of working with reflect is *)
  Local Open Scope nat.
  Definition act_is_from_account (act : Action) : Prop :=
    address_is_contract (act_from act) = false.

  Definition act_origin_is_account (act : Action) : Prop :=
    address_is_contract (act_origin act) = false.

  Definition act_origin_is_eq_from (act : Action) : Prop :=
    address_eqb (act_origin act) (act_from act) = true.

  Record IsValidNextBlock (header : BlockHeader) (chain : Chain) : Prop :=
    build_is_valid_next_block {
      valid_height : block_height header = S (chain_height chain);
      valid_slot : block_slot header > current_slot chain;
      valid_finalized_height :
        block_finalized_height header >= finalized_height chain /\
        block_finalized_height header < block_height header;
      valid_creator : address_is_contract (block_creator header) = false;
      valid_reward : (block_reward header >= 0)%Z;
    }.

  Record ChainState :=
    build_chain_state {
      chain_state_env :> Environment;
      chain_state_queue : list Action;
    }.

  MetaRocq Run (make_setters ChainState).

  
  Inductive ActionChainStep (prev_bstate next_bstate : ChainState) :=
  | action_step_action :
      forall (act : Action)
             (acts : list Action)
             (new_acts : list Action),
        prev_bstate.(chain_state_queue) = act :: acts ->
        ActionEvaluation prev_bstate act next_bstate new_acts ->
        next_bstate.(chain_state_queue) = new_acts ++ acts ->
        ActionChainStep prev_bstate next_bstate.

  Definition ActionChainTrace := ChainedList ChainState ActionChainStep.

  Lemma action_trace_step_trace {from mid to} :
    ActionChainStep from mid ->
    ActionChainTrace mid to ->
    inhabited (ActionChainTrace from to).
  Proof.
    intros step trace.
    generalize dependent step. generalize dependent from.
    induction trace.
    - intros * step. constructor. eapply snoc; eauto. apply clnil.
    - intros * step. 
      destruct (IHtrace from0); auto.
      constructor; eapply snoc; eauto.
  Qed.

  Ltac destruct_action_chain_step :=
    match goal with
    | [step: ActionChainStep _ _ |- _] =>
      destruct step as
        [?act ?acts ?new_acts ?queue_prev ?eval ?queue_new]
    end.

  (* ChainStep with InternalChainTrace *) 
  Inductive ChainStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
  | step_block :
      forall (header : BlockHeader),
        chain_state_queue prev_bstate = [] ->
        IsValidNextBlock header prev_bstate ->
        Forall act_is_from_account (chain_state_queue next_bstate) ->
        Forall act_origin_is_eq_from (chain_state_queue next_bstate) ->
        EnvironmentEquiv
          next_bstate
          (add_new_block_to_env header prev_bstate) ->
        ChainStep prev_bstate next_bstate
  | step_action :
      forall  (act : Action)
              (acts : list Action),
        prev_bstate.(chain_state_queue) = act :: acts -> 
        next_bstate.(chain_state_queue) = acts ->     
        ActionChainTrace prev_bstate next_bstate -> 
        ChainStep prev_bstate next_bstate
  | step_action_invalid :
      forall (act : Action)
             (acts : list Action),
        EnvironmentEquiv next_bstate prev_bstate ->
        chain_state_queue prev_bstate = act :: acts ->
        chain_state_queue next_bstate = acts ->
        (forall bstate,
          bstate.(chain_state_queue) = acts ->
          ActionChainTrace prev_bstate bstate -> 
                                               False) -> 
        ChainStep prev_bstate next_bstate.
        
  Lemma origin_is_account acts :
    Forall act_is_from_account acts ->
    Forall act_origin_is_eq_from acts ->
    Forall act_origin_is_account acts.
  Proof.
    intros Hall.
    induction Hall as [| a Ha]; intros Hall0; auto.
    inversion Hall0; subst.
    constructor; auto.
    specialize (address_eqb_spec (act_origin a) (act_from a)) as Haddr;
      unfold act_origin_is_eq_from in *; destruct Haddr; easy.
  Qed.

  Definition empty_state : ChainState :=
    {| chain_state_env :=
        {| env_chain :=
              {| chain_height := 0;
                current_slot := 0;
                finalized_height := 0; |};
            env_account_balances a := 0%Z;
            env_contract_states a := None;
            env_contracts a := None; |};
      chain_state_queue := [] |}.

  (* The ChainTrace captures that there is a valid execution where,
  starting from one environment and queue of actions, we end up in a
  different environment and queue of actions. *)
  Definition ChainTrace := ChainedList ChainState ChainStep.

  (* Additionally, a state is reachable if there is a trace ending in this trace. *)
  Definition reachable (bstate : ChainState) : Prop := 
    inhabited (ChainTrace empty_state bstate).

  Definition outgoing_acts (state : ChainState) (addr : Address) : list ActionBody :=
    map act_body
        (filter (fun act => (act_from act =? addr)%address) (chain_state_queue state)).

  (* We define a transaction as a "fully specified" action, recording all info. For
  example, a transaction contains the contract address that was created when a contract
  is deployed. This is more about bridging the gap between our definitions and what
  a normal blockchain is. Each evaluation of an action in the blockchain corresponds to
  a transaction, so we can go from a trace to a list of transactions. *)
  Inductive TxBody :=
    | tx_empty
    | tx_deploy (wc : WeakContract) (setup : SerializedValue)
    | tx_call (msg : option SerializedValue).

  Record Tx :=
    build_tx {
        tx_limit : nat;
        tx_origin : Address;
        tx_from : Address;
        tx_to : Address;
        tx_amount : Amount;
        tx_body : TxBody;
    }.

  Definition eval_tx {pre : Environment} {act : Action}
                    {post : Environment} {new_acts : list Action}
                    (step : ActionEvaluation pre act post new_acts) : Tx :=
    match step with
    | eval_transfer limit origin from to amount _ _ _ _ _ _ _ =>
      build_tx limit origin from to amount tx_empty
    | eval_deploy limit origin from to amount wc setup _ _ _ _ _ _ _ _ _ _ =>
      build_tx limit origin from to amount (tx_deploy wc setup)
    | eval_call limit origin from to amount _ msg _ _ _ _ _ _ _ _ _ _ _ _ =>
      build_tx limit origin from to amount (tx_call msg)
    end.
    
  Fixpoint act_trace_txs {from to : ChainState} (trace : ActionChainTrace from to) : list Tx :=
    match trace with
    | snoc trace' step =>
      match step with
      | action_step_action _ _ _ _ _ _ eval _ => eval_tx eval :: act_trace_txs trace'
      end
    | _ => []
    end.

  Fixpoint trace_txs {from to : ChainState} (trace : ChainTrace from to) : list Tx :=
    match trace with
    | snoc trace' step =>
      match step with
      | step_action _ _ _ _ _ _ action_trace => act_trace_txs action_trace ++ trace_txs trace'
      | _ => trace_txs trace'
      end
    | _ => []
    end.

  Definition at_incoming_txs
           {from to : ChainState}
           (trace : ActionChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_to tx =? addr)%address) (act_trace_txs trace).

  Definition incoming_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_to tx =? addr)%address) (trace_txs trace).

Definition outgoing_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_from tx =? addr)%address) (trace_txs trace).


Record ContractCallInfo (Msg : Type) :=
  build_call_info
  {
    call_origin : Address;
    call_from : Address;
    call_amount : Amount;
    call_msg : option Msg;
  }.

Global Arguments build_call_info {_}.
Global Arguments call_origin {_}.
Global Arguments call_from {_}.
Global Arguments call_amount {_}.
Global Arguments call_msg {_}.

  Fixpoint act_trace_incoming_calls
            (Msg : Type) `{Serializable Msg}
            {from to : ChainState}
            (trace : ActionChainTrace from to)
            (caddr : Address) : option (list (ContractCallInfo Msg)) :=
    match trace with
    | snoc trace' step =>
      match step with
      | action_step_action _ _ _ _ _ _ (eval_call _ origin from to amount _ msg _ _ _ _ _ _ _ _ _ _ _ _) _ =>
        if (to =? caddr)%address then
          (* If there is a message it should deserialize correctly,
            otherwise the entire operation returns None. *)
          do hd_msg <- match msg with
                      | Some msg =>
                        match deserialize msg with
                        | Some msg => Some (Some msg)
                        | None => None
                        end
                      | None => Some None
                      end;
          do tl <- act_trace_incoming_calls Msg trace' caddr;
          Some (build_call_info origin from amount hd_msg :: tl)
        else
          act_trace_incoming_calls Msg trace' caddr
      | _ => act_trace_incoming_calls Msg trace' caddr
      end
    | _ => Some []
    end.
    
  Fixpoint incoming_calls
            (Msg : Type) `{Serializable Msg}
            {from to : ChainState}
            (trace : ChainTrace from to)
            (caddr : Address) : option (list (ContractCallInfo Msg)) :=
    match trace with
    | snoc trace' step =>
      match step with
      | step_action _ _ _ _ _ _ action_trace =>
        do l1 <- act_trace_incoming_calls Msg action_trace caddr;
        do tl <- incoming_calls Msg trace' caddr;
        Some (l1 ++ tl)
      | _ => incoming_calls Msg trace' caddr
      end
    | _ => Some []
    end.

  Record DeploymentInfo (Setup : Type) :=
    build_deployment_info
    {
      deployment_origin : Address;
      deployment_from : Address;
      deployment_amount : Amount;
      deployment_setup : Setup;
    }.

  Global Arguments build_deployment_info {_}.
  Global Arguments deployment_origin {_}.
  Global Arguments deployment_from {_}.
  Global Arguments deployment_amount {_}.
  Global Arguments deployment_setup {_}.

  Fixpoint act_trace_deployment_info
            (Setup : Type) `{Serializable Setup}
            {from to : ChainState}
            (trace : ActionChainTrace from to)
            (caddr : Address) : option (DeploymentInfo Setup) :=
    match trace with
    | snoc trace' step =>
      match step with
      | action_step_action _ _ _ _ _ _ (eval_deploy limit origin from to amount _ setup _ _ _ _ _ _ _ _ _ _) _ =>
        if (to =? caddr)%address then
          do setup <- deserialize setup;
          Some (build_deployment_info origin from amount setup)
        else
          act_trace_deployment_info Setup trace' caddr
      | _ => act_trace_deployment_info Setup trace' caddr
      end
    | clnil => None
    end.

  Fixpoint deployment_info
            (Setup : Type) `{Serializable Setup}
            {from to : ChainState}
            (trace : ChainTrace from to)
            (caddr : Address) : option (DeploymentInfo Setup) :=
    match trace with
    | snoc trace' step =>
      match step with
      | step_action _ _ _ _ _ _ action_trace =>
        match (act_trace_deployment_info Setup action_trace caddr) with
        | Some dep_info => Some dep_info
        | None =>
          deployment_info Setup trace' caddr
        end
      | _ => deployment_info Setup trace' caddr
      end
    | clnil => None
    end.  

  Fixpoint trace_blocks {from to : ChainState}
          (trace : ChainTrace from to) : list BlockHeader :=
    match trace with
    | snoc trace' step =>
      match step with
      | step_block _ _ header _ _ _ _ _ =>
        header :: trace_blocks trace'
      | _ => trace_blocks trace'
      end
    | clnil => []
    end.

  Definition created_blocks
            {from to : ChainState} (trace : ChainTrace from to)
            (creator : Address) : list BlockHeader :=
    filter (fun b => (block_creator b =? creator)%address)
          (trace_blocks trace).

  Definition is_deploy (ac : ActionBody) : bool :=
    match ac with
    | act_transfer _ _ => false
    | act_call _ _ _ => false
    | act_deploy _ _ _ => true
    end.

  Definition is_call (ac : ActionBody) : bool :=
    match ac with
    | act_transfer _ _ => false
    | act_call _ _ _ => true
    | act_deploy _ _ _ => false
    end.

  Definition is_transfer (ac : ActionBody) : bool :=
    match ac with
    | act_transfer _ _ => true
    | act_call _ _ _ => false
    | act_deploy _ _ _ => false
    end.

Section Theories.
  Ltac destruct_chain_step :=
    match goal with
    | [step: ChainStep _ _ |- _] =>
      destruct step as
        [?header ?queue_prev ?valid_header ?acts_from_accs ?origin_correct ?env_eq|
         ?act ?acts ?queue_prev ?queue_new ?action_trace|
         ?act ?acts ?env_eq ?queue_prev ?queue_new ?no_action_trace]
    end.

  Ltac destruct_action_eval :=
    match goal with
    | [eval: ActionEvaluation _ _ _ _ |- _] => destruct eval
    end.

  Lemma trace_reachable : forall {to},
      ChainTrace empty_state to ->
        reachable to.
  Proof.
    constructor.
    assumption.
  Qed.

  Lemma contract_addr_format {to} (addr : Address) (wc : WeakContract) :
    reachable to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros [trace] contract_at_addr.
    remember empty_state eqn:eq.
    induction trace; rewrite eq in *; clear eq.
    - cbn in *; congruence.
    - specialize (IHtrace ltac:(auto)).
      destruct_chain_step;
        try now rewrite_environment_equiv.
      assert (A : forall bstate, ActionChainTrace mid bstate -> env_contracts bstate addr = Some wc -> address_is_contract addr = true).
      {
        intros * trace'. remember mid eqn:eq'; induction trace'; rewrite eq' in *; clear eq'; auto.
        specialize_hypotheses.
        intros contract_at_addr'.
        destruct_action_chain_step.
        destruct_action_eval; rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
      }
      apply (A to); auto.
  Qed.

  Lemma new_acts_no_out_queue limit orig addr1 addr2 new_acts resp_acts :
    addr1 <> addr2 ->
    new_acts = map (build_act limit orig addr2) resp_acts ->
    Forall (fun a => (act_from a =? addr1)%address = false) new_acts.
  Proof.
    intros neq ?; subst.
    induction resp_acts; cbn; auto.
    constructor; destruct_address_eq; cbn in *; congruence.
  Qed.

  Lemma outgoing_acts_after_block_nil bstate addr :
    Forall act_is_from_account (chain_state_queue bstate) ->
    address_is_contract addr = true ->
    outgoing_acts bstate addr = [].
  Proof.
    intros all is_contract.
    unfold outgoing_acts.
    induction (chain_state_queue bstate); auto.
    cbn.
    inversion_clear all.
    destruct_address_eq; subst; auto.
    unfold act_is_from_account in *.
    congruence.
  Qed.

  Lemma outgoing_acts_after_deploy_nil bstate addr :
    Forall (fun act => (act_from act =? addr)%address = false) (chain_state_queue bstate) ->
    outgoing_acts bstate addr = [].
  Proof.
    intros all.
    unfold outgoing_acts.
    induction (chain_state_queue bstate) as [|hd tl IH]; auto.
    cbn in *.
    inversion_clear all.
    rewrite H.
    auto.
  Qed.

  
  Lemma preserve_action_trace : 
    forall (from to : ChainState) 
           (P : forall (bstate : ChainState), Prop),
      (forall (prev next : ChainState),
        ActionChainStep prev next ->
        P prev ->
        P next)       ->
      reachable from ->
      ActionChainTrace from to ->
      P from ->
      P to.
  Proof.
    intros * preserve reach internaltrace Hfrom.
    induction internaltrace; auto.
    apply preserve with mid; auto.
  Qed.

  Ltac case_step_action :=
    match goal with
    | [action_trace : ActionChainTrace ?mid ?to |- _] => 
      pattern to; apply (preserve_action_trace mid to); auto;
      intros * ?step ?IHprev; destruct_action_chain_step
    end.

  Local Hint Unfold reachable : core.

  Local Open Scope address.
  (* This next lemma shows that any for a full chain trace,
  the ending state will not have any queued actions from
  undeployed contracts. *)
  Lemma undeployed_contract_no_out_queue contract state :
    reachable state ->
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    Forall (fun act => (act_from act =? contract) = false) (chain_state_queue state).
  Proof.
    intros [trace] is_contract.
    remember empty_state eqn:eq.
    induction trace;
      intros undeployed; rewrite eq in *; clear eq; cbn; auto.
    destruct_chain_step.
    - (* Add_block *)
      match goal with
      | [H: Forall act_is_from_account _ |- _] => induction H
      end;
      match goal with
      | [H: Forall act_origin_is_eq_from _ |- _] => inversion H
      end; constructor; auto; destruct_address_eq; congruence.
    - generalize dependent undeployed.
      case_step_action.
      intros.
      repeat
        match goal with
        | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
        end;
      subst;
      cbn in *.
      destruct_action_eval; rewrite_environment_equiv; subst; auto.
      all: cbn in *; specialize_hypotheses.
      + eapply Forall_cons_iff; eauto.
      + destruct (address_eqb contract to_addr); try congruence. eapply Forall_cons_iff; eauto.
      + apply Forall_app.
        assert (contract <> to_addr) by congruence.
        split; [eapply new_acts_no_out_queue|eapply Forall_cons_iff]; eauto.
    - (* Invalid User Action *)
      rewrite_environment_equiv.
        repeat
          match goal with
          | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
          end;
        subst;
        cbn in *.
      now apply Forall_inv_tail in IHtrace.
  Qed.

  Local Hint Resolve contracts_post_pre_none : core.
  Local Hint Unfold reachable : core.

  Lemma at_undeployed_contract_no_out_queue 
        contract from to (trace : ActionChainTrace from to) :
    reachable from ->
    address_is_contract contract = true ->
    env_contracts to contract = None ->
    Forall (fun act => (act_from act =? contract) = false) (chain_state_queue to).
  Proof.
    intros reach is_contract.
    remember from eqn:eq.
    induction trace;
      intros undeployed; rewrite eq in *; clear eq; cbn; auto.
    - (* base *)
      apply (undeployed_contract_no_out_queue contract from); auto.
    - (* induction *)
      destruct_action_chain_step.
      destruct_action_eval;
        try rewrite_environment_equiv;
        repeat
          match goal with
          | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
          end;
        subst;
        cbn in *.
      + (* Transfer step, just use IH *)
        eapply Forall_cons_iff; eauto.
      + (* Deploy step. First show that it is not to contract and then use IH. *)
        destruct_address_eq; try congruence.
        eapply Forall_cons_iff; eauto.
      + (* Call. Show that it holds for new actions as it is from *)
        (* another contract, and use IH for remaining. *)
        apply Forall_app.
        assert (contract <> to_addr) by congruence.
        split; [eapply new_acts_no_out_queue|eapply Forall_cons_iff]; eauto.
  Qed.

  (* action_trace *)
  Lemma at_undeployed_contract_no_out_txs
        contract from to (trace : ActionChainTrace from to) :
    reachable from ->
    address_is_contract contract = true ->
    env_contracts to contract = None ->
    filter (fun tx => (tx_from tx =? contract)%address) (act_trace_txs trace) = [].
  Proof.
    intros * reach is_contract undeployed.
    remember from; induction trace; subst; cbn; auto.
    destruct_action_chain_step. 
    cbn.
    
    pose proof 
         (at_undeployed_contract_no_out_queue
            contract from mid trace
            ltac:(auto) ltac:(auto) ltac:(eauto)) as Hqueue.
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
      end.
    inversion_clear Hqueue.
    destruct act;
    destruct_action_eval; rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      try tauto; try congruence.
  Qed.

   
  Lemma at_contract_not_disapear 
        contract from to (trace : ActionChainTrace from to) :
    reachable from ->
    env_contracts to contract = None ->
    env_contracts from contract = None.
  Proof.
    intros reach.
    remember from; induction trace; subst; auto.
    specialize_hypotheses. intro undeployed.
    destruct_action_chain_step.
    apply IHtrace.
    destruct_action_eval; try rewrite_environment_equiv; cbn in *; auto.
    destruct_address_eq; subst; cbn in *; auto.
  Qed.

  (* With this lemma proven, we can show that the (perhaps seemingly stronger)
  fact, that an undeployed contract has no outgoing txs, holds. *)
  Lemma undeployed_contract_no_out_txs
        contract state (trace : ChainTrace empty_state state) :
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    outgoing_txs trace contract = [].
  Proof.
    intros is_contract undeployed.
    remember empty_state; induction trace; subst; cbn; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    - (* In these steps we will use that the queue did not contain txs to the contract. *)
      specialize_hypotheses.
      rewrite filter_app. fold (outgoing_txs trace contract).
      rewrite (at_undeployed_contract_no_out_txs contract mid to action_trace); auto.
      cbn.
      apply IHtrace.
      eapply at_contract_not_disapear; eauto.
  Qed.

  Lemma at_undeployed_contract_no_in_txs
          contract from to (trace : ActionChainTrace from to) :
    reachable from ->
    address_is_contract contract = true ->
    env_contracts to contract = None ->
    filter (fun tx : Tx => (tx_to tx =? contract)%address) (act_trace_txs trace) = [].
  Proof.
    intros * reach is_contract undeployed.
    remember from; induction trace; subst; cbn; auto.
    destruct_action_chain_step. specialize_hypotheses. 
    destruct_action_eval; rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      try tauto; try congruence.
  Qed.

  Lemma undeployed_contract_no_in_txs
        contract state (trace : ChainTrace empty_state state) :
    address_is_contract contract = true ->
    env_contracts state contract = None ->
    incoming_txs trace contract = [].
  Proof.
    intros is_contract undeployed.
    remember empty_state; induction trace; subst; cbn; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    rewrite filter_app. unfold incoming_txs in *.
    rewrite at_undeployed_contract_no_in_txs; cbn; auto.
    specialize_hypotheses. rewrite IHtrace; auto.
    eapply at_contract_not_disapear; eauto.
  Qed.

  Lemma at_deployment_info_some
        Setup `{Serializable Setup}
        {from to} (trace : ActionChainTrace from to) caddr :
    reachable from ->
    act_trace_deployment_info Setup trace caddr <> None ->
    env_contracts to caddr <> None.
  Proof.
    intros * reach is_contract undeployed.
    remember from; induction trace; subst; cbn; auto.
    destruct_action_chain_step. specialize_hypotheses. 
    destruct_action_eval; rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      try tauto; try congruence.
  Qed.

  Lemma deployment_info_some
        Setup `{Serializable Setup}
        {to} (trace : ChainTrace empty_state to) caddr :
    deployment_info Setup trace caddr <> None ->
    env_contracts to caddr <> None.
  Proof.
    remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *; try tauto.
    destruct_chain_step; try now rewrite_environment_equiv.
    specialize_hypotheses. intros Hdep_info.
    destruct (act_trace_deployment_info Setup action_trace caddr) eqn:dep_info.
    - (* info *)
      apply (at_deployment_info_some Setup action_trace); auto. congruence.
    - (* no info *)
      specialize (at_contract_not_disapear caddr mid to) as H1; auto.
      unfold not; intros. specialize_hypotheses. congruence.
  Qed.

  Lemma deployment_info_addr_format
        Setup `{Serializable Setup} {to}
        (trace : ChainTrace empty_state to)
        caddr :
    deployment_info Setup trace caddr <> None ->
    address_is_contract caddr = true.
  Proof.
    intros has_deployment_info.
    pose proof (deployment_info_some _ _ _ has_deployment_info).
    destruct (env_contracts to caddr) as [wc|] eqn:?; try congruence.
    eapply contract_addr_format; eauto.
  Qed.

  Lemma list_cons_not {T:Type} (x : T) (l : list T) :
    ~ l = x :: l. 
  Proof.
    generalize dependent x. induction l; auto. unfold not in *. intros.
    inversion H. apply IHl with x; auto.
  Qed.

  Ltac solve_list_cons_not :=
    match goal with
    | [H: ?l = ?x :: ?l |- _] => apply list_cons_not in H; auto
      end.

  Lemma at_undeployed_contract_no_in_calls
        {Msg} `{Serializable Msg}
        contract from to (trace : ActionChainTrace from to) :
    reachable from ->
    env_contracts to contract = None ->
    act_trace_incoming_calls Msg trace contract = Some [].
  Proof.
    intros * reach undeployed.
    remember from; induction trace; subst; cbn; auto.
    destruct_action_chain_step. specialize_hypotheses. 
    destruct_action_eval; rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      try tauto; try congruence.   
  Qed.

  Lemma undeployed_contract_no_in_calls
        {Msg} `{Serializable Msg}
        contract state (trace : ChainTrace empty_state state) :
    env_contracts state contract = None ->
    incoming_calls Msg trace contract = Some [].
  Proof.
    unfold incoming_calls.
    intros undeployed.
    remember empty_state; induction trace; subst; cbn in *; auto.
    destruct_chain_step; try now rewrite_environment_equiv.
    specialize (at_undeployed_contract_no_in_calls contract mid to action_trace ltac:(auto) ltac:(auto)) as L.
    rewrite L. cbn. 
    assert (env_contracts mid contract = None). { eapply at_contract_not_disapear; eauto. }
    specialize_hypotheses.
    rewrite IHtrace. auto.
  Qed.

  Local Open Scope Z.
  Lemma at_account_balance_trace from to (trace : ActionChainTrace from to) addr :
    env_account_balances to addr =
    env_account_balances from addr +
    sumZ tx_amount (filter (fun tx : Tx => (tx_to tx =? addr)%address) (act_trace_txs trace)) -
    sumZ tx_amount (filter (fun tx : Tx => (tx_from tx =? addr)%address)(act_trace_txs trace)).
  Proof.
    remember from; induction trace; subst; cbn; auto. lia.
    destruct_action_chain_step. specialize_hypotheses. 
    destruct_action_eval; cbn in *; rewrite_environment_equiv; cbn in *.
    all: rewrite IHtrace by auto.
    all: destruct_address_eq; subst; cbn in *; try lia.
  Qed.   

  Lemma account_balance_trace state (trace : ChainTrace empty_state state) addr :
    env_account_balances state addr =
    sumZ tx_amount (incoming_txs trace addr) +
    sumZ block_reward (created_blocks trace addr) -
    sumZ tx_amount (outgoing_txs trace addr).
  Proof.
    unfold incoming_txs, outgoing_txs.
    remember empty_state as from_state.
    induction trace; [|destruct_chain_step].
    - subst. cbn. lia.
    - (* Block *)
      rewrite_environment_equiv.
      cbn.
      fold (created_blocks trace addr).
      rewrite IHtrace by auto.
      destruct_address_eq; subst; cbn; lia.
    - (* Step *)
      cbn.
      repeat rewrite filter_app. repeat rewrite sumZ_app.
      rewrite (at_account_balance_trace mid to action_trace addr).
      specialize_hypotheses. rewrite IHtrace.
      fold (created_blocks trace addr). lia.
    - (* Invalid User Action *)
      now rewrite_environment_equiv.
  Qed.

  Lemma contract_no_created_blocks state (trace : ChainTrace empty_state state) addr :
    address_is_contract addr = true ->
    created_blocks trace addr = [].
  Proof.
    intros is_contract.
    remember empty_state eqn:eq.
    induction trace; auto.
    destruct_chain_step; auto.
    cbn.
    subst.
    inversion valid_header.
    destruct (address_eqb_spec (block_creator header) addr); auto.
    congruence.
  Qed.

  Lemma at_undeployed_contract_balance_0 from to addr :
    reachable from ->
    env_account_balances from addr = 0 ->
    ActionChainTrace from to ->
    address_is_contract addr = true ->
    env_contracts to addr = None ->
    env_account_balances to addr = 0.
  Proof.
    intros reach Hfrom trace is_contract no_contract.
    rewrite (at_account_balance_trace _ _ trace); auto.
    rewrite at_undeployed_contract_no_out_txs; auto.
    rewrite at_undeployed_contract_no_in_txs; auto.
    cbn. lia.
  Qed.

  Lemma undeployed_contract_balance_0 state addr :
    reachable state ->
    address_is_contract addr = true ->
    env_contracts state addr = None ->
    env_account_balances state addr = 0.
  Proof.
    intros [trace] is_contract no_contract.
    rewrite (account_balance_trace _ trace); auto.
    rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
            contract_no_created_blocks; auto.
  Qed.

  Lemma account_balance_nonnegative state addr :
    reachable state ->
    env_account_balances state addr >= 0.
  Proof.
    intros [trace].
    remember empty_state eqn:eq.
    induction trace; subst; cbn; try lia.
    specialize (IHtrace eq_refl).
    destruct_chain_step.
    - (* New block *)
      rewrite_environment_equiv.
      cbn.
      inversion valid_header.
      destruct_address_eq; lia.
    - (* Action evaluation *)
      assert (at_account_balance_nonnegative : 
        forall st, ActionChainTrace mid st -> env_account_balances st addr >= 0).
      {
        intros * trace'.
        remember mid; induction trace'; subst; cbn; auto.
        destruct_action_chain_step. specialize_hypotheses. 
        destruct_action_eval; rewrite_environment_equiv;
          subst;
          cbn in *;
          destruct_address_eq; cbn; subst; lia.
      }
      apply at_account_balance_nonnegative; auto.
    - (* Invalid User Action *)
      now rewrite_environment_equiv.
  Qed.

  Lemma wc_init_strong
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {chain ctx setup result} :
    wc_init (contract : WeakContract) chain ctx setup = Ok result ->
    exists setup_strong result_strong,
      deserialize setup = Some setup_strong /\
      serialize result_strong = result /\
      Blockchain.init contract chain ctx setup_strong = Ok result_strong.
  Proof.
    intros init.
    cbn in *.
    destruct (deserialize setup) as [setup_strong|] eqn:deser_setup;
      cbn in *; try congruence.
    exists setup_strong.
    destruct (Blockchain.init _ _ _ _) as [result_strong|] eqn:result_eq;
      cbn in *; try congruence.
    exists result_strong.
    repeat split; auto with congruence.
  Qed.

  Lemma wc_receive_strong
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {chain ctx prev_state msg new_state new_acts} :
    wc_receive (contract : WeakContract) chain ctx prev_state msg =
    Ok (new_state, new_acts) ->
    exists prev_state_strong msg_strong new_state_strong,
      deserialize prev_state = Some prev_state_strong /\
      match msg_strong with
      | Some msg_strong => msg >>= deserialize = Some msg_strong
      | None => msg = None
      end /\
      serialize new_state_strong = new_state /\
      Blockchain.receive contract chain ctx prev_state_strong msg_strong =
      Ok (new_state_strong, new_acts).
  Proof.
    intros receive.
    cbn in *.
    destruct (deserialize prev_state) as [prev_state_strong|] eqn:deser_state;
      cbn in *; try congruence.
    exists prev_state_strong.
    exists (msg >>= deserialize).
    destruct msg as [msg|]; cbn in *.
    1: destruct (deserialize msg) as [msg_strong|];
      cbn in *; try congruence.
    all: destruct (Blockchain.receive _ _ _ _ _)
      as [[resp_state_strong resp_acts_strong]|] eqn:result_eq;
      cbn in *; try congruence.
    all: exists resp_state_strong.
    all: inversion_clear receive; auto.
  Qed.

  Lemma deployed_contract_state_typed
            {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
            {contract : Contract Setup Msg State Error}
            {bstate : ChainState}
            {caddr} :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    reachable bstate ->
    exists (cstate : State),
      contract_state bstate caddr = Some cstate.
  Proof.
    intros contract_deployed [trace].
    destruct (contract_state bstate caddr) as [cstate|] eqn:eq;
      [exists cstate; auto|].
    unfold contract_state in *.
    (* Show that eq is a contradiction. *)
    remember empty_state; induction trace; subst; cbn in *; try congruence.
    destruct_chain_step; try now rewrite_environment_equiv.
    assert (at_deployed_contract_state_typed :
           forall {st : ChainState},
        env_contracts st caddr = Some (contract : WeakContract) ->
        ActionChainTrace mid st ->
        exists (cstate : State),
          contract_state st caddr = Some cstate).
    {
      (* ActionChainTrace *)
      intros st contract_deployed' trace'.
      destruct (contract_state st caddr) as [cstate|] eqn:eq';
        [exists cstate; auto|].
      unfold contract_state in *.
      (* Show that eq is a contradiction. *)
      remember mid; induction trace'; subst; cbn in *; try congruence.
      { specialize_hypotheses. auto. }
      destruct_action_chain_step. specialize_hypotheses. 
      destruct_action_eval; subst; rewrite_environment_equiv; cbn in *.
      - (* Transfer, use IH *)
        auto.
      - (* Deployment *)
        destruct_address_eq; subst; auto.
        (* To this contract, show that deserialization would not fail. *)
        replace wc with (contract : WeakContract) in * by congruence.
        destruct (wc_init_strong ltac:(eassumption))
          as [setup_strong [result_strong [? [<- init]]]].
        cbn in eq'.
        rewrite deserialize_serialize in eq'; congruence.
      - (* Call *)
        destruct (address_eqb_spec caddr to_addr); subst; auto.
        (* To this contract, show that deserialization would not fail. *)
        replace wc with (contract : WeakContract) in * by congruence.
        destruct (wc_receive_strong ltac:(eassumption))
          as [state_strong [msg_strong [resp_state_strong [? [? [<- receive]]]]]].
        cbn in eq'.
        rewrite deserialize_serialize in eq'; congruence.
    }
    destruct (at_deployed_contract_state_typed to contract_deployed action_trace) as (cstate & Hstate).
    cbn in *. rewrite Hstate in *. congruence.
  Qed.

  Lemma origin_is_always_account {bstate : ChainState} :
    reachable bstate ->
    Forall act_origin_is_account (chain_state_queue bstate).
  Proof.
    intros [trace].
    remember empty_state; induction trace; subst; cbn in *; try constructor.
    destruct_chain_step.
    - (* New block, use the fact that [act_origin] is the same as [act_from]
        and [act_from] is an account address*)
      now apply origin_is_account.
    - (* Action evaluation *)
      assert (at_origin_is_always_account :
        forall st, ActionChainTrace mid st ->
          Forall act_origin_is_account (chain_state_queue st)).
      {
        intros st trace'.
        remember mid; induction trace'; subst; cbn in *; auto.
        destruct_action_chain_step. specialize_hypotheses. 
        destruct_action_eval;  
        repeat
          match goal with
          | [H: chain_state_queue _ = _ |- _] => rewrite H in *
          end;
        subst; cbn in *; specialize_hypotheses;
        inversion IHtrace'; subst; try easy.
        apply Forall_app. split; auto.
        apply All_Forall.Forall_map.
        apply Forall_forall; easy.
      }
      specialize_hypotheses. auto.
    - (* Invalid User Action *)
      rewrite queue_new in *; rewrite queue_prev in *; cbn in *.
      specialize_hypotheses; inversion IHtrace; subst; easy.
  Qed.

   
  Lemma queue_from_account : forall (st : ChainState),
    reachable st ->
    Forall act_is_from_account st.(chain_state_queue).
  Proof.
    intros * [trace].
    remember empty_state; induction trace as [|? mid to ? IH step]; subst; cbn; auto.
    specialize (IH ltac:(auto)).
    destruct_chain_step; auto.
    - (* step_action *)
      subst. rewrite queue_prev in *. apply Forall_cons_iff in IH as [_ ?]; auto.
    - (* step_action_invalid *)
      subst. rewrite queue_prev in *. apply Forall_cons_iff in IH as [_ ?]; auto.
  Qed.

  
  Definition incoming_calls_in_action_trace
            (Msg : Type) `{Serializable Msg}
            {from mid to : ChainState}
            (trace : ChainTrace from mid)
            (action_trace : ActionChainTrace mid to)
            (caddr : Address) : option (list (ContractCallInfo Msg)) :=
    do l1 <- act_trace_incoming_calls Msg action_trace caddr;
    do l2 <- incoming_calls Msg trace caddr; 
    Some (l1 ++ l2).

  Definition deployment_info_in_action_trace
            (Setup : Type) `{Serializable Setup}
            {from mid to : ChainState}
            (trace : ChainTrace from mid)
            (action_trace : ActionChainTrace mid to)
            (caddr : Address) : option (DeploymentInfo Setup) :=
    match act_trace_deployment_info Setup action_trace caddr with
    | Some dep_info => Some dep_info
    | None => deployment_info Setup trace caddr
    end.

  Definition incoming_txs_in_action_trace
           {from mid to : ChainState}
           (trace : ChainTrace from mid)
           (action_trace : ActionChainTrace mid to)
           (addr : Address) : list Tx :=
    filter (fun tx => (tx_to tx =? addr)%address) (act_trace_txs action_trace ++ trace_txs trace).

  Lemma undeployed_contract_no_dep_info
        Setup `{Serializable Setup}
        {bstate} (trace : ChainTrace empty_state bstate) caddr :
    env_contracts bstate caddr = None -> 
    deployment_info Setup trace caddr = None.
  Proof.
    remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *; try tauto.
    destruct_chain_step; try now rewrite_environment_equiv.
    specialize_hypotheses. intros Hdep_info.
    assert (at_undeployed_contract_no_dep_info : forall st
        (action_trace : ActionChainTrace mid st),
      env_contracts st caddr = None -> 
      act_trace_deployment_info Setup action_trace caddr = None 
      ).
    {
        intros * ?.
        remember mid; induction action_trace0; subst; cbn; auto.
        destruct_action_chain_step. specialize_hypotheses. 
        destruct_action_eval; rewrite_environment_equiv;
          subst;
          cbn in *;
          destruct_address_eq; cbn; subst; auto.
        congruence.
    }
    rewrite at_undeployed_contract_no_dep_info; auto.
    apply IH. eapply at_contract_not_disapear; eauto.
  Qed.

  Lemma incoming_txs_contract
        caddr bstate (trace : ChainTrace empty_state bstate)
        Setup `{Serializable Setup} (depinfo : DeploymentInfo Setup)
        Msg `{Serializable Msg} (msgs : list (ContractCallInfo Msg)) :
    deployment_info Setup trace caddr = Some depinfo ->
    incoming_calls Msg trace caddr = Some msgs ->
    map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) (incoming_txs trace caddr) =
    map (fun call => (call_from call, caddr, call_amount call)) msgs ++
        [(deployment_from depinfo, caddr, deployment_amount depinfo)].
  Proof.
    intros depinfo_eq calls_eq.
    
    enough ((env_contracts bstate caddr = None ->
            incoming_txs trace caddr = [] /\
            deployment_info Setup trace caddr = None /\
            incoming_calls Msg trace caddr = Some []) /\
            (env_contracts bstate caddr <> None ->
            deployment_info Setup trace caddr <> None ->
            incoming_calls Msg trace caddr <> None ->
            exists (depinfo : DeploymentInfo Setup)
                    (inc_calls : list (ContractCallInfo Msg))
                    (call_txs : list Tx) (dep_tx : Tx),
              deployment_info Setup trace caddr = Some depinfo /\
              incoming_calls Msg trace caddr = Some inc_calls /\
              incoming_txs trace caddr = call_txs ++ [dep_tx] /\
              map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) call_txs =
              map (fun call => (call_from call, caddr, call_amount call)) inc_calls /\
              (tx_from dep_tx, tx_to dep_tx, tx_amount dep_tx) =
              (deployment_from depinfo, caddr, deployment_amount depinfo))) as generalized.
    {
      rewrite depinfo_eq, calls_eq in *.
      destruct (env_contracts bstate caddr).
      - destruct generalized as [_ generalized].
        specialize (generalized ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
        destruct generalized as [? [? [? [? [? [? [-> [? ?]]]]]]]].
        rewrite map_app.
        cbn.
        congruence.
      - destruct generalized as [generalized _].
        specialize (generalized eq_refl).
        destruct generalized as [_ [? _]]; congruence.
    }
    assert (is_contract: address_is_contract caddr = true).
    { assert (deployment_info Setup trace caddr <> None) by congruence.
      eapply (deployment_info_addr_format Setup); eassumption. }
    clear depinfo_eq calls_eq depinfo msgs.
    remember empty_state; induction trace as [| ? mid to trace IH step]; subst; cbn in *;
      try tauto.
    assert (at_incoming_txs_contract : forall bstate (action_trace : ActionChainTrace mid bstate),
      (env_contracts bstate caddr = None ->
       incoming_txs_in_action_trace trace action_trace caddr = [] /\
       deployment_info_in_action_trace Setup trace action_trace caddr = None /\
       incoming_calls_in_action_trace Msg trace action_trace caddr = Some []) /\
      (env_contracts bstate caddr <> None ->
       deployment_info_in_action_trace Setup trace action_trace caddr <> None ->
       incoming_calls_in_action_trace Msg trace action_trace caddr <> None ->
       exists (depinfo0 : DeploymentInfo Setup) (inc_calls : list (ContractCallInfo Msg)) (call_txs : list Tx) (dep_tx : Tx),
        deployment_info_in_action_trace Setup trace action_trace caddr = Some depinfo0 /\
        incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
        incoming_txs_in_action_trace trace action_trace caddr = call_txs ++ [dep_tx] /\
        map (fun tx : Tx => (tx_from tx, tx_to tx, tx_amount tx)) call_txs =
          map (fun call : ContractCallInfo Msg => (call_from call, caddr, call_amount call)) inc_calls /\
        (tx_from dep_tx, tx_to dep_tx, tx_amount dep_tx) =
          (deployment_from depinfo0, caddr, deployment_amount depinfo0))).
    {
      (* clear depinfo_eq calls_eq. *)
      intros *.
      remember mid; induction action_trace as [| ? mid_at to_at action_trace' IH_at step_at]; subst; cbn in *.
      {
        (* clnil *)
        destruct (incoming_calls Msg trace caddr) eqn:calls_eq''; try congruence; auto.
      }
      specialize (IH_at ltac:(auto) trace ltac:(auto) ltac:(auto)) as (IH_at1 & IH_at2).
      destruct_action_chain_step; destruct_action_eval; cbn in *; rewrite_environment_equiv;
        unfold deployment_info_in_action_trace, incoming_txs_in_action_trace in *; try rewrite filter_app in *;
        cbn in *.
      - (* transfer *)  
        destruct_address_eq.
        + subst; cbn; congruence.
        + rewrite_environment_equiv; auto.
      - (* Deploy *)
        rewrite_environment_equiv; cbn in *.
        rewrite (address_eq_sym caddr) in *.
        destruct_address_eq; auto.
        subst to_addr.
        split; try discriminate.
        intros _ depinfo_ne_none calls_ne_none.
        cbn in *.
        rewrite undeployed_contract_no_dep_info in depinfo_ne_none; auto.
        2: eapply at_contract_not_disapear; eauto.
        destruct (deserialize setup); cbn in *; try congruence.
        remember (build_deployment_info _ _ _ _) as depinfo.
        remember (build_tx _ _ _ _ _ _) as deptx.
        specialize (IH_at1 ltac:(auto)).
        fold (incoming_txs trace caddr).
        destruct IH_at1 as (? & ? & ?). unfold incoming_txs in *.
        exists depinfo, [], [], deptx; subst; cbn in *.
        repeat split; auto. rewrite H1. auto.  
      - (* Call *)
        rewrite_environment_equiv; cbn in *.
        rewrite (address_eq_refl to_addr) in *.
        destruct (address_eqb_spec to_addr caddr); auto.
        subst. cbn in *.
        split; [intros; congruence|].
        intros ? deploy_info calls.
        destruct (match msg with | Some _ => _ | _ => Some None end);
          cbn in *; try congruence.
        destruct (act_trace_incoming_calls Msg action_trace' caddr); cbn in *; try congruence.
        destruct (incoming_calls _ _) as [inc_calls|]; cbn in *; try congruence.
        specialize (IH_at2 ltac:(auto) ltac:(auto) ltac:(auto)).
        destruct IH_at2 as (depinfo & prev_calls & prev_call_txs & dep_tx &
          depinfo_eq & inc_calls_eq & inc_txs_eq & map_eq & dep_eq).
        remember (build_tx _ _ _ _ _ _) as new_tx.
        remember (build_call_info _ _ _ _) as new_call.
        exists depinfo, (new_call :: l0 ++ inc_calls), (new_tx :: prev_call_txs), dep_tx.
        split; auto.
        split; auto.
        fold (incoming_txs trace caddr) in *.
        rewrite inc_txs_eq.
        split; [now rewrite app_comm_cons|].
        inversion inc_calls_eq. rewrite H3.
        cbn.
        rewrite map_eq.
        subst; tauto.
    }
    destruct_chain_step; cbn in *; try now rewrite_environment_equiv.

    specialize (at_incoming_txs_contract to action_trace) as (L1 & L2). 
    unfold deployment_info_in_action_trace, incoming_txs_in_action_trace in *; try rewrite filter_app in *; cbn in *.
    split; auto.
  Qed.

  Inductive TagFacts := tag_facts.
  Inductive TagAddBlock := tag_add_block.
  Inductive TagDeployment := tag_deployment.
  Inductive TagOutgoingAct := tag_outgoing_act.
  Inductive TagNonrecursiveCall := tag_nonrecursive_call.
  Inductive TagRecursiveCall := tag_recursive_call.
  Inductive TagActionTraceFacts := tag_action_trace_facts.

  Hint Constructors
    TagFacts TagActionTraceFacts TagAddBlock TagDeployment TagOutgoingAct
    TagNonrecursiveCall TagRecursiveCall : core.

  Lemma contract_induction
      {Setup Msg State Error : Type}
     `{Serializable Setup}
     `{Serializable Msg}
     `{Serializable State}
     `{Serializable Error}
      (contract : Contract Setup Msg State Error)
      (AddBlockFacts :
         forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop)
      (DeployFacts : forall (chain : Chain) (ctx : ContractCallContext), Prop)
      (CallFacts :
         forall (chain : Chain)
                (ctx : ContractCallContext)
                (cstate : State)
                (outgoing_actions : list ActionBody)
                (inc_calls : option (list (ContractCallInfo Msg))), Prop)
      (P : forall (chain_height : nat)
                  (current_slot : nat)
                  (finalized_height : nat)
                  (caddr : Address)
                  (deployment_info : DeploymentInfo Setup)
                  (cstate : State)
                  (balance : Amount)
                  (outgoing_actions_queued : list ActionBody)
                  (incoming_calls_seen : list (ContractCallInfo Msg))
                  (outgoing_txs_seen : list Tx), Prop) :

  (* Facts *)
  (
    (forall (bstate_from bstate_to : ChainState) (step : ChainStep bstate_from bstate_to)
            (from_reachable : ChainTrace empty_state bstate_from)
            (tag : TagFacts),
        match step with
        | step_block _ _ header _ _ _ _ _ =>
          AddBlockFacts (chain_height bstate_from)
                        (current_slot bstate_from)
                        (finalized_height bstate_from)
                        (block_height header)
                        (block_slot header)
                        (block_finalized_height header)
        | _ => Logic.True
        end) /\

    (forall (bstate_from bstate_mid bstate_to : ChainState) (step : ActionChainStep bstate_mid bstate_to)
            (from_reachable : ChainTrace empty_state bstate_from)
            (mid_action_reachable : ActionChainTrace bstate_from bstate_mid)
            (tag : TagActionTraceFacts),
        match step with
        | action_step_action _ _ act _ _ _ (eval_deploy limit origin from to amount _  _ _ _ _ _ _ _ _ _ _ _) _ =>
          DeployFacts
            (transfer_balance from to amount bstate_mid)
            (build_ctx limit origin from to amount amount)
        | action_step_action _ _ act _ _ _ (eval_call limit origin from to amount _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
          let new_state := transfer_balance from to amount bstate_mid in
          forall (cstate : State),
            env_contracts bstate_mid to = Some (contract : WeakContract) ->
            contract_state bstate_mid to = Some cstate ->
            CallFacts
              new_state
              (build_ctx limit origin from to (env_account_balances new_state to) amount) cstate
              (outgoing_acts bstate_mid to)
              (incoming_calls_in_action_trace Msg from_reachable mid_action_reachable to)
        | _ => Logic.True
        end)
   ) ->  

  (* Add block *)
  (forall old_chain_height old_cur_slot old_fin_height
          new_chain_height new_cur_slot new_fin_height
          caddr dep_info state balance inc_calls out_txs
          (facts : AddBlockFacts old_chain_height old_cur_slot old_fin_height
                                 new_chain_height new_cur_slot new_fin_height)
          (IH : P old_chain_height old_cur_slot old_fin_height
                  caddr dep_info state balance [] inc_calls out_txs)
          (tag : TagAddBlock),
      P new_chain_height new_cur_slot new_fin_height
        caddr dep_info state balance [] inc_calls out_txs) ->

  (* Deploy contract *)
  (forall chain ctx setup result
          (facts : DeployFacts chain ctx)
          (init_some : init contract chain ctx setup = Ok result)
          (tag : TagDeployment),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
        result
        (ctx_amount ctx)
        []
        []
        []) ->

  (* Transfer/call/deploy to someone else *)
  (forall height slot fin_height caddr dep_info cstate
          balance out_act out_acts inc_calls prev_out_txs tx
          (IH : P height slot fin_height caddr dep_info cstate balance
                  (out_act :: out_acts) inc_calls prev_out_txs)
          (tx_from_caddr : tx_from tx = caddr)
          (tx_amount_eq : tx_amount tx = act_body_amount out_act)
          (tx_act_match :
             match out_act with
             | act_transfer to amount =>
               tx_to tx = to /\ tx_amount tx = amount /\
               (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
             | act_deploy amount wc setup =>
               tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
             | act_call to amount msg =>
               tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg)
             end)
          (tag : TagOutgoingAct),
      P height slot fin_height caddr dep_info cstate (balance - act_body_amount out_act)
        out_acts inc_calls (tx :: prev_out_txs)) ->

  (* Non-recursive call *)
  (forall chain ctx dep_info prev_state msg
          prev_out_queue prev_inc_calls prev_out_txs
          new_state new_acts
          (from_other : ctx_from ctx <> ctx_contract_address ctx)
          (facts : CallFacts chain ctx prev_state prev_out_queue (Some prev_inc_calls))
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (ctx_contract_address ctx) dep_info prev_state
                  (ctx_contract_balance ctx - ctx_amount ctx)
                  prev_out_queue prev_inc_calls prev_out_txs)
          (receive_some : receive contract chain ctx prev_state msg =
                          Ok (new_state, new_acts))
          (tag : TagNonrecursiveCall),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        dep_info
        new_state
        (ctx_contract_balance ctx)
        (new_acts ++ prev_out_queue)
        (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
        prev_out_txs) -> 

  (* Recursive call *)
  (forall chain ctx dep_info prev_state msg
          head prev_out_queue prev_inc_calls prev_out_txs
          new_state new_acts
          (from_self : ctx_from ctx = ctx_contract_address ctx)
          (facts : CallFacts chain ctx prev_state (head :: prev_out_queue) (Some prev_inc_calls))
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (ctx_contract_address ctx) dep_info prev_state
                  (ctx_contract_balance ctx)
                  (head :: prev_out_queue) prev_inc_calls prev_out_txs)
          (action_facts :
             match head with
             | act_transfer to amount => to = ctx_contract_address ctx /\
                                         amount = ctx_amount ctx /\
                                         msg = None
             | act_call to amount msg_ser => to = ctx_contract_address ctx /\
                                             amount = ctx_amount ctx /\
                                             msg <> None /\
                                             deserialize msg_ser = msg
             | _ => False
             end)
          (receive_some : receive contract chain ctx prev_state msg =
                          Ok (new_state, new_acts))
          (tag : TagRecursiveCall), 
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (ctx_contract_address ctx)
        dep_info
        new_state
        (ctx_contract_balance ctx)
        (new_acts ++ prev_out_queue)
        (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
        (build_tx (ctx_limit ctx)
                  (ctx_origin ctx)
                  (ctx_from ctx)
                  (ctx_contract_address ctx)
                  (ctx_amount ctx)
                  (tx_call (match head with
                            | act_call _ _ msg => Some msg
                            | _ => None
                            end)) :: prev_out_txs)) ->

  forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists dep cstate inc_calls,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      P (chain_height bstate)
        (current_slot bstate)
        (finalized_height bstate)
        caddr
        dep
        cstate
        (env_account_balances bstate caddr)
        (outgoing_acts bstate caddr)
        inc_calls
        (outgoing_txs trace caddr).
  Proof.
    intros (establish_facts & at_establish_facts)
           add_block_case
           init_case
           transfer_case
           nonrecursive_call_case
           recursive_call_case
           bstate caddr trace contract_deployed.
    assert (address_is_contract caddr = true) as is_contract
        by (eapply contract_addr_format; eauto).
    unfold contract_state in *.
    remember empty_state; induction trace as [|? ? ? ? IH];
      intros; subst; try solve [cbn in *; congruence].
    specialize (IH ltac:(auto) ltac:(auto) ltac:(auto)).
    specialize (establish_facts mid to ltac:(auto) ltac:(auto) tag_facts).
    destruct_chain_step;
      [|clear add_block_case; cbn in *|].
    - (* New block *)
      clear init_case recursive_call_case nonrecursive_call_case.
      rewrite_environment_equiv.
      specialize_hypotheses.
      cbn in *.
      destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
      exists depinfo', cstate', inc_calls'.
      rewrite_environment_equiv.
      repeat split; auto.
      inversion valid_header.
      cbn in *.
      destruct_address_eq; try congruence.
      rewrite outgoing_acts_after_block_nil by auto.
      unfold outgoing_acts in *; rewrite queue_prev in *; cbn in *.
      eapply add_block_case; try constructor.
      + apply establish_facts. 
      + assumption.
    - (* step_action *)
      assert (
        at_contract_induction : forall st
              (action_trace : ActionChainTrace mid st),
          env_contracts st caddr = Some (contract : WeakContract) ->
          exists
              (dep : DeploymentInfo Setup) 
              (cstate : State) 
              (inc_calls : list (ContractCallInfo Msg)),
            match act_trace_deployment_info Setup action_trace caddr with
            | Some dep_info => Some dep_info
            | None => deployment_info Setup trace caddr
            end = Some dep /\
            match env_contract_states st caddr with
            | Some val => deserialize val
            | None => None
            end = Some cstate /\
            incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
            P (chain_height st) (current_slot st) (finalized_height st) caddr dep
              cstate (env_account_balances st caddr) (outgoing_acts st caddr)
              inc_calls
              (filter (fun tx : Tx => (tx_from tx =? caddr)%address)
                (act_trace_txs action_trace ++ trace_txs trace))
      ).
      {
        intros st action_trace' contract_deployed'.
        remember mid; induction action_trace' as [|? at_mid at_to action_trace' IHat at_step]; subst; cbn in *; auto.
        {
          (* clnil *)
          specialize_hypotheses.
          destruct IH as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
          exists depinfo', cstate', inc_calls'.
          repeat split; auto.
        }
        specialize (at_establish_facts mid at_mid at_to at_step trace action_trace' tag_action_trace_facts).
        (* specialize (at_establish_facts mid at_mid at_to at_step). *)
        destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv; cbn in *.
        - (* Evaluation: transfer *)
          clear init_case recursive_call_case nonrecursive_call_case.
          specialize (IHat ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)). 
          destruct IHat as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
          exists depinfo', cstate', inc_calls'.
          rewrite_environment_equiv.
          repeat split; auto.
          rewrite (address_eq_sym from_addr) in *.
          cbn in *.
          (* Transfer cannot be to contract as that would be a
          call. Resolve this now. *)
          destruct (address_eqb_spec caddr to_addr) as [->|];
            cbn in *; try congruence.
          unfold outgoing_acts in *.
          rewrite queue_prev0, queue_new in *.
          match goal with
          | [ H : act0 = _ |- _ ] => rewrite H in *
          end.
          subst.
          cbn in *.
          rewrite (address_eq_sym from_addr) in *.
          destruct (address_eqb_spec caddr from_addr) as [<-|];
            cbn in *.
          + (* Transfer from contract *)
            remember (act_transfer _ _) as out_act.
            replace (-amount + env_account_balances at_mid caddr) with
                (env_account_balances at_mid caddr - act_body_amount out_act) by
                (subst; cbn; lia).
            subst.
            apply transfer_case; auto.
          + (* Irrelevant transfer *)
            auto.
        - (* Evaluation: Deploy *)
          clear recursive_call_case nonrecursive_call_case.
          rewrite (address_eq_sym to_addr caddr) in *.
          destruct (address_eqb_spec caddr to_addr) as [<-|]; cbn in *.
          + (* Deployment of this contract *)
            replace wc with (contract : WeakContract) in * by congruence.
            match goal with
            | [ H : wc_init _ _ _ _ = Ok _ |- _ ] =>
              destruct (wc_init_strong H) as (setup_strong & result_strong & deser_setup_eq & <- & init)
            end.
            rewrite deser_setup_eq in *.
            exists (build_deployment_info origin from_addr amount setup_strong),
                  result_strong,
                  [].
            rewrite_environment_equiv; cbn.
            rewrite address_eq_refl.
            cbn.
            rewrite deserialize_serialize.
            assert (undeployed : env_contracts mid caddr = None)
              by (eapply (at_contract_not_disapear caddr mid at_mid); eauto).
            assert (incoming_calls Msg trace caddr = Some [])
              by (eapply undeployed_contract_no_in_calls; eauto).
            assert (act_trace_incoming_calls Msg action_trace' caddr = Some [])
              by (apply at_undeployed_contract_no_in_calls; auto).
            unfold incoming_calls in *. rewrite is_contract in *.
            repeat split; cbn in *; subst; cbn; auto. 
            {
              rewrite H3, H4. auto.
            }
            unfold outgoing_acts.
            rewrite queue_new; cbn.
            rewrite (address_eq_sym caddr) in *.
            repeat rewrite filter_app.
            fold (outgoing_txs trace caddr).
            assert (queue_ne_to : 
              Forall (fun (act : Action) => (act_from act =? caddr)%address = false) (chain_state_queue at_mid)).
            {
              eapply at_undeployed_contract_no_out_queue; eauto.
            }
            rewrite queue_prev0 in queue_ne_to.
            inversion_clear queue_ne_to as [|? ? from_ne_to rest_ne_to].
            cbn in from_ne_to.
            cbn in *.
            rewrite (address_eq_ne from_addr caddr) by (destruct_address_eq; auto).
            rewrite Forall_false_filter_nil by assumption.
            rewrite undeployed_contract_no_out_txs; auto.
            rewrite at_undeployed_contract_no_out_txs; auto.
            assert (env_account_balances mid caddr = 0).
            {
              eapply undeployed_contract_balance_0; auto.
            }
            rewrite (at_undeployed_contract_balance_0 mid); auto.
            remember (build_ctx _ _ _ _ _ _) as ctx.
            replace origin with (ctx_origin ctx) by (subst; auto).
            replace from_addr with (ctx_from ctx) by (subst; auto).
            replace caddr with (ctx_contract_address ctx) by (subst; auto).
            replace amount with (ctx_amount ctx) by (subst; auto).
            cbn. 
            rewrite Z.add_0_r.
            apply init_case; auto.
          + (* Deployment of other contract, might be by this contract. *)
            specialize (IHat ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)). 
            destruct IHat as (depinfo & cstate & inc_calls & -> & ? & -> & ?).
            exists depinfo, cstate, inc_calls.
            rewrite_environment_equiv; cbn.
            rewrite address_eq_ne by auto.
            repeat split; auto.
            rewrite (address_eq_sym caddr).
            unfold outgoing_acts in *.
            rewrite queue_prev0, queue_new in *.
            match goal with
            | [ H : act0 = _ |- _ ] => rewrite H in *
            end.
            subst new_acts.
            cbn in *.
            repeat rewrite filter_app in *. fold (outgoing_txs trace caddr) in *.
            destruct_address_eq; subst; cbn in *; auto. 
            (* This contract deploys other contract *)
            remember (act_deploy _ _ _) as abody.
            replace (-amount + env_account_balances at_mid caddr)
              with (env_account_balances at_mid caddr - act_body_amount abody)
              by (subst; cbn; lia).
            subst.
            apply transfer_case; auto.
        - (* Evaluation: Call *)
          clear init_case.
          specialize (IHat ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
          match goal with
            | [ H : act0 = _ |- _ ] => rewrite H in *
          end.
          subst new_acts.
          destruct IHat as (depinfo & cstate & inc_calls & -> & ? & inc_calls_eq & IHat).
          unfold outgoing_acts in *.
          rewrite queue_prev0, queue_new in *.
          cbn in *.
          repeat rewrite filter_app.
          rewrite filter_map, map_app, map_map; cbn in *.
          destruct (address_eqb_spec to_addr caddr) as [->|].
          + (* Call to this contract *)
            replace wc with (contract : WeakContract) in * by congruence.
            destruct (wc_receive_strong ltac:(eassumption))
              as (prev_state_strong & msg_strong & resp_state_strong &
                  deser_state & deser_msg & <- & receive).
            replace (env_contract_states at_mid caddr) with (Some prev_state) in * by auto.
            cbn in *.
            replace prev_state_strong with cstate in * by congruence; clear prev_state_strong.
            exists depinfo, resp_state_strong.
            exists (build_call_info origin from_addr amount msg_strong :: inc_calls).
            rewrite_environment_equiv.
            cbn.
            rewrite address_eq_refl.
            cbn.
            rewrite deserialize_serialize.
            rewrite filter_app in *.
            repeat split; auto.
            {
              destruct msg_strong as [msg_strong|], msg as [msg|]; cbn in *; try congruence.
              - rewrite deser_msg.
                destruct (act_trace_incoming_calls Msg action_trace' caddr) eqn:Hat.
                +
                destruct (incoming_calls Msg trace caddr); cbn in *; try congruence.
                +
                destruct (incoming_calls Msg trace caddr); cbn in *; try congruence.
              - destruct (act_trace_incoming_calls Msg action_trace' caddr); try congruence.
                destruct (incoming_calls Msg trace caddr); cbn in *; try congruence.
            }
            rewrite (address_eq_sym caddr), filter_true, map_id.
            destruct (address_eqb_spec from_addr caddr) as [->|?]; cbn in *.
            all: rewrite (address_eq_refl caddr) in *.
            * (* Recursive call *)
            remember (build_ctx _ _ _ _ _ _) as ctx.
            pose proof
                (recursive_call_case
                  (transfer_balance caddr caddr amount at_mid)
                  ctx depinfo cstate msg_strong
                  (match msg with
                    | Some msg => act_call caddr amount msg
                    | None => act_transfer caddr amount
                    end)) as case.
            subst ctx.
            cbn in case.
            replace (-amount + (amount + env_account_balances at_mid caddr))
              with (env_account_balances at_mid caddr)
              in * by lia.
            destruct msg_strong as [msg_strong|], msg as [msg|];
              cbn in *; try congruence.
            -- replace (deserialize msg) with (Some msg_strong) in * by auto.
              apply case; auto.
              rewrite <- inc_calls_eq.
              specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
              eapply at_establish_facts.
            --
              apply case; auto.
              rewrite <- inc_calls_eq.
              specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
              eapply at_establish_facts.
          * (* Someone else calls contract *)
            remember (build_ctx _ _ _ _ _ _) as ctx.
            pose proof
                (nonrecursive_call_case
                  (transfer_balance from_addr caddr amount at_mid)
                  ctx depinfo cstate msg_strong) as case.
            subst ctx.
            cbn in case.
            rewrite (address_eq_ne caddr from_addr) in * by (subst; auto).
            replace (amount + env_account_balances at_mid caddr - amount)
              with (env_account_balances at_mid caddr) in case
              by lia.
            fold (outgoing_txs trace caddr).
            apply case; auto.
            rewrite <- inc_calls_eq.
            specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
            eapply at_establish_facts.
          + (* Call to other contract *) 
            exists depinfo, cstate, inc_calls.
            rewrite_environment_equiv.
            rewrite filter_false.
            cbn.
            rewrite address_eq_ne by auto.
            rewrite (address_eq_sym caddr).
            destruct (address_eqb_spec from_addr caddr) as [->|?].
            * (* Call from us to other contract *)
              repeat split; auto.
              rewrite filter_app in *; fold (outgoing_txs trace caddr) in *.
              cbn in *.
              destruct msg as [msg|].
              1: remember (act_call _ _ _) as abody.
              2: remember (act_transfer _ _) as abody.
              1, 2: replace (-amount + env_account_balances at_mid caddr)
                with (env_account_balances at_mid caddr - act_body_amount abody)
                by (subst; cbn; lia).
              1, 2: subst; apply transfer_case; auto.
            * (* Irrelevant call. *)
              rewrite filter_app in *; fold (outgoing_txs trace caddr) in *.
              auto.
      }
      eapply at_contract_induction; auto.
    - (* Invalid User Action *)
      rewrite_environment_equiv.
      destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH); auto.
      exists depinfo, cstate, inc_calls.
      repeat split; try rewrite_environment_equiv; auto. cbn.
      assert (outgoing_acts_eq : outgoing_acts mid caddr = outgoing_acts to caddr).
      { unfold outgoing_acts.
        setoid_rewrite queue_new.
        setoid_rewrite queue_prev.
        f_equal.
        cbn.
        specialize (queue_from_account mid ltac:(auto)) as from_accs.
        rewrite queue_prev in from_accs.
        apply Forall_cons_iff in from_accs as (from_acc & _).
        destruct_address_eq; easy.
      }
      rewrite outgoing_acts_eq in IH.
      cbn.
      now fold (outgoing_txs trace caddr).
  Qed.

  
  Definition reachable_in_action_trace mid to := 
    reachable mid /\ inhabited (ActionChainTrace mid to). 

  
  Lemma contract_addr_format_action_trace {from to} (addr : Address) (wc : WeakContract) :
    reachable_in_action_trace from to ->
    env_contracts to addr = Some wc ->
    address_is_contract addr = true.
  Proof.
    intros (reach & [trace]) contract_at_addr.
    remember from; induction trace; subst; cbn in *.
    { eapply contract_addr_format; eauto. }
    specialize_hypotheses.
      destruct_action_chain_step; destruct_action_eval;
        try now rewrite_environment_equiv; auto.
    rewrite_environment_equiv. cbn in *.
    destruct_address_eq; subst; cbn in *; auto.
  Qed.

  
  Lemma account_balance_nonnegative_action_trace origin state addr :
    reachable_in_action_trace origin state ->
    env_account_balances state addr >= 0.
  Proof.
    intros ([trace] & [action_trace]).
    remember origin; induction action_trace; subst; cbn in *.
    { eapply account_balance_nonnegative; auto. }
    destruct_action_chain_step. specialize_hypotheses. 
    destruct_action_eval; rewrite_environment_equiv;
      subst; cbn in *; destruct_address_eq; cbn; subst; lia.
  Qed.

  Lemma action_trace_step {from to} :
    ActionChainTrace from to ->
    from = to \/
    exists mid, inhabited (ActionChainStep from mid) /\ inhabited (ActionChainTrace mid to).
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

  Definition outgoing_txs_in_action_trace
           {from mid to : ChainState}
           (trace : ChainTrace from mid)
           (action_trace : ActionChainTrace mid to)
           (addr : Address) : list Tx :=
    filter (fun tx => (tx_from tx =? addr)%address) (act_trace_txs action_trace ++ trace_txs trace).

  Local Hint Unfold reachable_in_action_trace : core.

  Lemma contract_induction_action_trace
      {Setup Msg State Error : Type}
     `{Serializable Setup}
     `{Serializable Msg}
     `{Serializable State}
     `{Serializable Error}
      (contract : Contract Setup Msg State Error)
      (AddBlockFacts :
         forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop)
      (DeployFacts : forall (chain : Chain) (ctx : ContractCallContext), Prop)
      (CallFacts :
         forall (chain : Chain)
                (ctx : ContractCallContext)
                (cstate : State)
                (outgoing_actions : list ActionBody)
                (inc_calls : option (list (ContractCallInfo Msg))), Prop)
      (P : forall (chain_height : nat)
                  (current_slot : nat)
                  (finalized_height : nat)
                  (caddr : Address)
                  (deployment_info : DeploymentInfo Setup)
                  (cstate : State)
                  (balance : Amount)
                  (outgoing_actions_queued : list ActionBody)
                  (incoming_calls_seen : list (ContractCallInfo Msg))
                  (outgoing_txs_seen : list Tx), Prop) : 

    (* Facts *)
    (
      (forall (bstate_from bstate_to : ChainState) (step : ChainStep bstate_from bstate_to)
              (from_reachable : ChainTrace empty_state bstate_from)
              (tag : TagFacts),
          match step with
          | step_block _ _ header _ _ _ _ _ =>
            AddBlockFacts (chain_height bstate_from)
                          (current_slot bstate_from)
                          (finalized_height bstate_from)
                          (block_height header)
                          (block_slot header)
                          (block_finalized_height header)
          | _ => Logic.True
          end) /\

      (forall (bstate_from bstate_mid bstate_to : ChainState) (step : ActionChainStep bstate_mid bstate_to)
              (from_reachable : ChainTrace empty_state bstate_from)
              (mid_action_reachable : ActionChainTrace bstate_from bstate_mid)
              (tag : TagActionTraceFacts),
          match step with
          | action_step_action _ _ act _ _ _ (eval_deploy limit origin from to amount _  _ _ _ _ _ _ _ _ _ _ _) _ =>
            DeployFacts
              (transfer_balance from to amount bstate_mid)
              (build_ctx limit origin from to amount amount)
          | action_step_action _ _ act _ _ _ (eval_call limit origin from to amount _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
            let new_state := transfer_balance from to amount bstate_mid in
            forall (cstate : State),
              env_contracts bstate_mid to = Some (contract : WeakContract) ->
              contract_state bstate_mid to = Some cstate ->
              CallFacts
                new_state
                (build_ctx limit origin from to (env_account_balances new_state to) amount) cstate
                (outgoing_acts bstate_mid to)
                (incoming_calls_in_action_trace Msg from_reachable mid_action_reachable to)
          | _ => Logic.True
          end)
    ) ->  

    (* Add block *)
    (forall old_chain_height old_cur_slot old_fin_height
            new_chain_height new_cur_slot new_fin_height
            caddr dep_info state balance inc_calls out_txs
            (facts : AddBlockFacts old_chain_height old_cur_slot old_fin_height
                                  new_chain_height new_cur_slot new_fin_height)
            (IH : P old_chain_height old_cur_slot old_fin_height
                    caddr dep_info state balance [] inc_calls out_txs)
            (tag : TagAddBlock),
        P new_chain_height new_cur_slot new_fin_height
          caddr dep_info state balance [] inc_calls out_txs) ->

    (* Deploy contract *)
    (forall chain ctx setup result
            (facts : DeployFacts chain ctx)
            (init_some : init contract chain ctx setup = Ok result)
            (tag : TagDeployment),
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
          result
          (ctx_amount ctx)
          []
          []
          []) ->

    (* Transfer/call/deploy to someone else *)
    (forall height slot fin_height caddr dep_info cstate
            balance out_act out_acts inc_calls prev_out_txs tx
            (IH : P height slot fin_height caddr dep_info cstate balance
                    (out_act :: out_acts) inc_calls prev_out_txs)
            (tx_from_caddr : tx_from tx = caddr)
            (tx_amount_eq : tx_amount tx = act_body_amount out_act)
            (tx_act_match :
              match out_act with
              | act_transfer to amount =>
                tx_to tx = to /\ tx_amount tx = amount /\
                (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
              | act_deploy amount wc setup =>
                tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
              | act_call to amount msg =>
                tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg)
              end)
            (tag : TagOutgoingAct),
        P height slot fin_height caddr dep_info cstate (balance - act_body_amount out_act)
          out_acts inc_calls (tx :: prev_out_txs)) ->

    (* Non-recursive call *)
    (forall chain ctx dep_info prev_state msg
            prev_out_queue prev_inc_calls prev_out_txs
            new_state new_acts
            (from_other : ctx_from ctx <> ctx_contract_address ctx)
            (facts : CallFacts chain ctx prev_state prev_out_queue (Some prev_inc_calls))
            (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                    (ctx_contract_address ctx) dep_info prev_state
                    (ctx_contract_balance ctx - ctx_amount ctx)
                    prev_out_queue prev_inc_calls prev_out_txs)
            (receive_some : receive contract chain ctx prev_state msg =
                            Ok (new_state, new_acts))
            (tag : TagNonrecursiveCall),
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          dep_info
          new_state
          (ctx_contract_balance ctx)
          (new_acts ++ prev_out_queue)
          (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
          prev_out_txs) -> 

    (* Recursive call *)
    (forall chain ctx dep_info prev_state msg
            head prev_out_queue prev_inc_calls prev_out_txs
            new_state new_acts
            (from_self : ctx_from ctx = ctx_contract_address ctx)
            (facts : CallFacts chain ctx prev_state (head :: prev_out_queue) (Some prev_inc_calls))
            (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                    (ctx_contract_address ctx) dep_info prev_state
                    (ctx_contract_balance ctx)
                    (head :: prev_out_queue) prev_inc_calls prev_out_txs)
            (action_facts :
              match head with
              | act_transfer to amount => to = ctx_contract_address ctx /\
                                          amount = ctx_amount ctx /\
                                          msg = None
              | act_call to amount msg_ser => to = ctx_contract_address ctx /\
                                              amount = ctx_amount ctx /\
                                              msg <> None /\
                                              deserialize msg_ser = msg
              | _ => False
              end)
            (receive_some : receive contract chain ctx prev_state msg =
                            Ok (new_state, new_acts))
            (tag : TagRecursiveCall), 
        P (chain_height chain)
          (current_slot chain)
          (finalized_height chain)
          (ctx_contract_address ctx)
          dep_info
          new_state
          (ctx_contract_balance ctx)
          (new_acts ++ prev_out_queue)
          (build_call_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: prev_inc_calls)
          (build_tx (ctx_limit ctx)
                    (ctx_origin ctx)
                    (ctx_from ctx)
                    (ctx_contract_address ctx)
                    (ctx_amount ctx)
                    (tx_call (match head with
                              | act_call _ _ msg => Some msg
                              | _ => None
                              end)) :: prev_out_txs)) ->

    forall bstate_origin bstate caddr 
        (trace : ChainTrace empty_state bstate_origin)
        (action_trace : ActionChainTrace bstate_origin bstate),
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      exists dep cstate inc_calls,
        deployment_info_in_action_trace Setup trace action_trace caddr = Some dep /\
        contract_state bstate caddr = Some cstate /\
        incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
        P (chain_height bstate)
          (current_slot bstate)
          (finalized_height bstate)
          caddr
          dep
          cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
          inc_calls
          (outgoing_txs_in_action_trace trace action_trace caddr). 
  Proof.
    intros 
          (* (establish_facts & at_establish_facts) *)
           establish_facts
           add_block_case
           init_case
           transfer_case
           nonrecursive_call_case
           recursive_call_case
           bstate_origin bstate caddr trace action_trace contract_deployed.
    assert (address_is_contract caddr = true) as is_contract.
    {
      eapply contract_addr_format_action_trace; eauto.
      split; eauto.
    }
    unfold contract_state in *.
    remember empty_state; induction trace as [|? ? ? ? IH];
      intros; subst.
    {
      (* empty_state = bstate_origin *)
      destruct (action_trace_step action_trace) as [|(? & [step] & [?])]; intros; subst; try solve [cbn in *; congruence].
      destruct_action_chain_step. cbn in *; congruence.
    }
    (* specialize (IH ltac:(auto) ltac:(auto) ltac:(auto)). *)
    (* specialize (establish_facts mid to ltac:(auto) ltac:(auto) tag_facts). *)

    


    assert (
      preserve_through_action_trace : forall st1 st2
            (trace : ChainTrace empty_state st1)
            (action_trace : ActionChainTrace st1 st2),
        (* (
          env_contracts st1 caddr = Some (contract : WeakContract) ->
          exists
              (dep : DeploymentInfo Setup) 
              (cstate : State) 
              (inc_calls : list (ContractCallInfo Msg)),
            match act_trace_deployment_info Setup action_trace caddr with
            | Some dep_info => Some dep_info
            | None => deployment_info Setup trace caddr
            end = Some dep /\
            match env_contract_states st1 caddr with
            | Some val => deserialize val
            | None => None
            end = Some cstate /\
            incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
            P (chain_height st1) (current_slot st1) (finalized_height st1) caddr dep
              cstate (env_account_balances st2 caddr) (outgoing_acts st2 caddr)
              inc_calls
              (filter (fun tx : Tx => (tx_from tx =? caddr)%address)
              (act_trace_txs action_trace ++ trace_txs trace))
        ) -> *)
        env_contracts st2 caddr = Some (contract : WeakContract) ->
        exists
            (dep : DeploymentInfo Setup) 
            (cstate : State) 
            (inc_calls : list (ContractCallInfo Msg)),
          match act_trace_deployment_info Setup action_trace caddr with
          | Some dep_info => Some dep_info
          | None => deployment_info Setup trace caddr
          end = Some dep /\
          match env_contract_states st2 caddr with
          | Some val => deserialize val
          | None => None
          end = Some cstate /\
          incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
          P (chain_height st2) (current_slot st2) (finalized_height st2) caddr dep
            cstate (env_account_balances st2 caddr) (outgoing_acts st2 caddr)
            inc_calls
            (filter (fun tx : Tx => (tx_from tx =? caddr)%address)
            (act_trace_txs action_trace ++ trace_txs trace))
    ).
    {
      intros st1 st2 trace' action_trace' contract_deployed'.
      remember st1; induction action_trace' as [|? at_mid at_to action_trace' IHat at_step]; 
        subst; cbn in *; auto.
      {
        (* clnil *) 
        specialize (contract_induction contract AddBlockFacts DeployFacts CallFacts P 
          establish_facts add_block_case init_case transfer_case nonrecursive_call_case recursive_call_case
          st1 caddr trace' ltac:(auto)) as Hcontract_induction.
        destruct (Hcontract_induction) as (dep & cstate & inc_calls & Hdep & Hctate & Hinc & HP).
        exists dep, cstate, inc_calls. repeat (split; auto). rewrite Hinc. auto.
        (* eapply contract_induction; cbn in *; eauto. *)
      }
      specialize (IHat ltac:(auto) trace').
      destruct establish_facts as (establish_facts & at_establish_facts).
      specialize (at_establish_facts st1 at_mid at_to at_step trace' action_trace' tag_action_trace_facts).
      (* specialize (at_establish_facts mid at_mid at_to at_step). *)
      destruct_action_chain_step; destruct_action_eval; rewrite_environment_equiv; cbn in *.
      - (* Evaluation: transfer *)
        clear init_case recursive_call_case nonrecursive_call_case.
        specialize (IHat ltac:(auto)). 
        destruct IHat as (depinfo' & cstate' & inc_calls' & -> & ? & -> & ?).
        exists depinfo', cstate', inc_calls'.
        rewrite_environment_equiv.
        repeat split; auto.
        rewrite (address_eq_sym from_addr) in *.
        cbn in *.
        (* Transfer cannot be to contract as that would be a
        call. Resolve this now. *)
        destruct (address_eqb_spec caddr to_addr) as [->|];
          cbn in *; try congruence.
        unfold outgoing_acts in *.
        rewrite queue_prev, queue_new in *.
        match goal with
        | [ H : act = _ |- _ ] => rewrite H in *
        end.
        subst.
        cbn in *.
        rewrite (address_eq_sym from_addr) in *.
        destruct (address_eqb_spec caddr from_addr) as [<-|];
          cbn in *.
        + (* Transfer from contract *)
          remember (act_transfer _ _) as out_act.
          replace (-amount + env_account_balances at_mid caddr) with
              (env_account_balances at_mid caddr - act_body_amount out_act) by
              (subst; cbn; lia).
          subst.
          apply transfer_case; auto.
        + (* Irrelevant transfer *)
          auto.
      - (* Evaluation: Deploy *)
        clear recursive_call_case nonrecursive_call_case.
        rewrite (address_eq_sym to_addr caddr) in *.
        destruct (address_eqb_spec caddr to_addr) as [<-|]; cbn in *.
        + (* Deployment of this contract *)
          replace wc with (contract : WeakContract) in * by congruence.
          match goal with
          | [ H : wc_init _ _ _ _ = Ok _ |- _ ] =>
            destruct (wc_init_strong H) as (setup_strong & result_strong & deser_setup_eq & <- & init)
          end.
          rewrite deser_setup_eq in *.
          exists (build_deployment_info origin from_addr amount setup_strong),
                result_strong,
                [].
          rewrite_environment_equiv; cbn.
          rewrite address_eq_refl.
          cbn.
          rewrite deserialize_serialize.
          assert (undeployed : env_contracts st1 caddr = None)
            by (eapply (at_contract_not_disapear caddr st1 at_mid); eauto).
          assert (incoming_calls Msg trace' caddr = Some [])
            by (eapply undeployed_contract_no_in_calls; eauto).
          assert (act_trace_incoming_calls Msg action_trace' caddr = Some [])
            by (apply at_undeployed_contract_no_in_calls; auto).
          unfold incoming_calls in *. rewrite is_contract in *.
          repeat split; cbn in *; subst; cbn; auto. 
          {
            rewrite H3, H4. auto.
          }
          unfold outgoing_acts.
          rewrite queue_new; cbn.
          rewrite (address_eq_sym caddr) in *.
          repeat rewrite filter_app.
          fold (outgoing_txs trace' caddr).
          assert (queue_ne_to : 
            Forall (fun (act : Action) => (act_from act =? caddr)%address = false) (chain_state_queue at_mid)).
          {
            eapply at_undeployed_contract_no_out_queue; eauto.
          }
          rewrite queue_prev in queue_ne_to.
          inversion_clear queue_ne_to as [|? ? from_ne_to rest_ne_to].
          cbn in from_ne_to.
          cbn in *.
          rewrite (address_eq_ne from_addr caddr) by (destruct_address_eq; auto).
          rewrite Forall_false_filter_nil by assumption.
          rewrite undeployed_contract_no_out_txs; auto.
          rewrite at_undeployed_contract_no_out_txs; auto.
          assert (env_account_balances st1 caddr = 0).
          {
            eapply undeployed_contract_balance_0; auto.
          }
          rewrite (at_undeployed_contract_balance_0 st1); auto.
          remember (build_ctx _ _ _ _ _ _) as ctx.
          replace origin with (ctx_origin ctx) by (subst; auto).
          replace from_addr with (ctx_from ctx) by (subst; auto).
          replace caddr with (ctx_contract_address ctx) by (subst; auto).
          replace amount with (ctx_amount ctx) by (subst; auto).
          cbn. 
          rewrite Z.add_0_r.
          apply init_case; auto.
        + (* Deployment of other contract, might be by this contract. *)
          specialize (IHat ltac:(auto)). 
          destruct IHat as (depinfo & cstate & inc_calls & -> & ? & -> & ?).
          exists depinfo, cstate, inc_calls.
          rewrite_environment_equiv; cbn.
          rewrite address_eq_ne by auto.
          repeat split; auto.
          rewrite (address_eq_sym caddr).
          unfold outgoing_acts in *.
          rewrite queue_prev, queue_new in *.
          match goal with
          | [ H : act = _ |- _ ] => rewrite H in *
          end.
          subst new_acts.
          cbn in *.
          repeat rewrite filter_app in *. fold (outgoing_txs trace' caddr) in *.
          destruct_address_eq; subst; cbn in *; auto. 
          (* This contract deploys other contract *)
          remember (act_deploy _ _ _) as abody.
          replace (-amount + env_account_balances at_mid caddr)
            with (env_account_balances at_mid caddr - act_body_amount abody)
            by (subst; cbn; lia).
          subst.
          apply transfer_case; auto.
      - (* Evaluation: Call *)
        clear init_case.
        specialize (IHat ltac:(auto)).
        match goal with
          | [ H : act = _ |- _ ] => rewrite H in *
        end.
        subst new_acts.
        destruct IHat as (depinfo & cstate & inc_calls & -> & ? & inc_calls_eq & IHat).
        unfold outgoing_acts in *.
        rewrite queue_prev, queue_new in *.
        cbn in *.
        repeat rewrite filter_app.
        rewrite filter_map, map_app, map_map; cbn in *.
        destruct (address_eqb_spec to_addr caddr) as [->|].
        + (* Call to this contract *)
          replace wc with (contract : WeakContract) in * by congruence.
          destruct (wc_receive_strong ltac:(eassumption))
            as (prev_state_strong & msg_strong & resp_state_strong &
                deser_state & deser_msg & <- & receive).
          replace (env_contract_states at_mid caddr) with (Some prev_state) in * by auto.
          cbn in *.
          replace prev_state_strong with cstate in * by congruence; clear prev_state_strong.
          exists depinfo, resp_state_strong.
          exists (build_call_info origin from_addr amount msg_strong :: inc_calls).
          rewrite_environment_equiv.
          cbn.
          rewrite address_eq_refl.
          cbn.
          rewrite deserialize_serialize.
          rewrite filter_app in *.
          repeat split; auto.
          {
            destruct msg_strong as [msg_strong|], msg as [msg|]; cbn in *; try congruence.
            - rewrite deser_msg.
              destruct (act_trace_incoming_calls Msg action_trace' caddr) eqn:Hat.
              +
              destruct (incoming_calls Msg trace' caddr); cbn in *; try congruence.
              +
              destruct (incoming_calls Msg trace' caddr); cbn in *; try congruence.
            - destruct (act_trace_incoming_calls Msg action_trace' caddr); try congruence.
              destruct (incoming_calls Msg trace' caddr); cbn in *; try congruence.
          }
          rewrite (address_eq_sym caddr), filter_true, map_id.
          destruct (address_eqb_spec from_addr caddr) as [->|?]; cbn in *.
          all: rewrite (address_eq_refl caddr) in *.
          * (* Recursive call *)
          remember (build_ctx _ _ _ _ _ _) as ctx.
          pose proof
              (recursive_call_case
                (transfer_balance caddr caddr amount at_mid)
                ctx depinfo cstate msg_strong
                (match msg with
                  | Some msg => act_call caddr amount msg
                  | None => act_transfer caddr amount
                  end)) as case.
          subst ctx.
          cbn in case.
          replace (-amount + (amount + env_account_balances at_mid caddr))
            with (env_account_balances at_mid caddr)
            in * by lia.
          destruct msg_strong as [msg_strong|], msg as [msg|];
            cbn in *; try congruence.
          -- replace (deserialize msg) with (Some msg_strong) in * by auto.
            apply case; auto.
            rewrite <- inc_calls_eq.
            specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
            eapply at_establish_facts.
          --
            apply case; auto.
            rewrite <- inc_calls_eq.
            specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
            eapply at_establish_facts.
        * (* Someone else calls contract *)
          remember (build_ctx _ _ _ _ _ _) as ctx.
          pose proof
              (nonrecursive_call_case
                (transfer_balance from_addr caddr amount at_mid)
                ctx depinfo cstate msg_strong) as case.
          subst ctx.
          cbn in case.
          rewrite (address_eq_ne caddr from_addr) in * by (subst; auto).
          replace (amount + env_account_balances at_mid caddr - amount)
            with (env_account_balances at_mid caddr) in case
            by lia.
          fold (outgoing_txs trace caddr).
          apply case; auto.
          rewrite <- inc_calls_eq.
          specialize (at_establish_facts cstate ltac:(auto) ltac:(auto) ).
          eapply at_establish_facts.
        + (* Call to other contract *) 
          exists depinfo, cstate, inc_calls.
          rewrite_environment_equiv.
          rewrite filter_false.
          cbn.
          rewrite address_eq_ne by auto.
          rewrite (address_eq_sym caddr).
          destruct (address_eqb_spec from_addr caddr) as [->|?].
          * (* Call from us to other contract *)
            repeat split; auto.
            rewrite filter_app in *; fold (outgoing_txs trace caddr) in *.
            cbn in *.
            destruct msg as [msg|].
            1: remember (act_call _ _ _) as abody.
            2: remember (act_transfer _ _) as abody.
            1, 2: replace (-amount + env_account_balances at_mid caddr)
              with (env_account_balances at_mid caddr - act_body_amount abody)
              by (subst; cbn; lia).
            1, 2: subst; apply transfer_case; auto.
          * (* Irrelevant call. *)
            rewrite filter_app in *; fold (outgoing_txs trace caddr) in *.
            auto.      
    }
    unfold contract_state in *. 
    specialize (preserve_through_action_trace to bstate (snoc trace l) action_trace ltac:(auto))
     as (dep & cstate & inc_calls & Hdep & Hcstate & Hinc & HP).
    exists dep, cstate, inc_calls. repeat (split; auto). 
  Qed.
  
  
  Lemma convert_contract_induction
      {Setup Msg State Error : Type}
     `{Serializable Setup}
     `{Serializable Msg}
     `{Serializable State}
     `{Serializable Error}
      {contract : Contract Setup Msg State Error}
      {AddBlockFacts :
         forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop}
      {DeployFacts : forall (chain : Chain) (ctx : ContractCallContext), Prop}
      {CallFacts :
         forall (chain : Chain)
                (ctx : ContractCallContext)
                (cstate : State)
                (outgoing_actions : list ActionBody)
                (inc_calls : option (list (ContractCallInfo Msg))), Prop}
      {P : forall (chain_height : nat)
                  (current_slot : nat)
                  (finalized_height : nat)
                  (caddr : Address)
                  (deployment_info : DeploymentInfo Setup)
                  (cstate : State)
                  (balance : Amount)
                  (outgoing_actions_queued : list ActionBody)
                  (incoming_calls_seen : list (ContractCallInfo Msg))
                  (outgoing_txs_seen : list Tx), Prop} : 
    (forall bstate_origin bstate caddr 
        (trace : ChainTrace empty_state bstate_origin)
        (action_trace : ActionChainTrace bstate_origin bstate),
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      exists dep cstate inc_calls,
        deployment_info_in_action_trace Setup trace action_trace caddr = Some dep /\
        contract_state bstate caddr = Some cstate /\
        incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
        P (chain_height bstate)
          (current_slot bstate)
          (finalized_height bstate)
          caddr
          dep
          cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
          inc_calls
          (outgoing_txs_in_action_trace trace action_trace caddr)) ->
    forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists dep cstate inc_calls,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      P (chain_height bstate)
        (current_slot bstate)
        (finalized_height bstate)
        caddr
        dep
        cstate
        (env_account_balances bstate caddr)
        (outgoing_acts bstate caddr)
        inc_calls
        (outgoing_txs trace caddr).
  Proof.
    intros Hat * contract_deployed.
    specialize (Hat bstate bstate caddr trace clnil contract_deployed).
    cbn in *. unfold outgoing_txs.
    destruct Hat as (dep & cstate & inc_calls & Hdep & Hcstate & Hinc & HP).
    exists dep, cstate, inc_calls.
    repeat (split; auto). destruct (incoming_calls Msg trace caddr); try congruence.
  Qed.

End Theories.
End Trace.
End Semantics.

  Inductive ActionEvaluationError :=
  | amount_negative (amount : Amount) (* amount is negative *)
  | amount_too_high (amount : Amount) (* sender does not have enough money *)
  | no_such_contract (addr : Address) (* there is no contract at that address *)
  | too_many_contracts (* cannot generate fresh address for new contract *)
  | init_failed (err : SerializedValue) (* contract init function failed *)
  | receive_failed (err : SerializedValue) (* contract receive function failed *)
  | deserialization_failed (val : SerializedValue) (* failed deserializing value *)
  | internal_error. (* unexpected internal error *)

  Inductive AddBlockError :=
  | invalid_header (header : BlockHeader) (* header for next block is invalid *)
  | invalid_root_action (act : Action) (* a specified root action is invalid *)
  | origin_from_mismatch (act : Action) (* origin and from addresses do not match for an action in a new block *)
  | action_evaluation_depth_exceeded (* out of fuel while evaluating actions recursively *)
  | action_evaluation_error (* error when evaluating single action *)
      (act : Action)
      (err : ActionEvaluationError).

  Class ChainBuilderType :=
    build_builder {
      builder_type : Type;

      builder_initial : builder_type;

      builder_env : builder_type -> Environment;

      builder_add_block
        (builder : builder_type)
        (header : BlockHeader)
        (actions : list Action) :
        result builder_type AddBlockError;

      builder_trace (builder : builder_type) :
        ChainTrace empty_state (build_chain_state (builder_env builder) []);
    }.

  Global Coercion builder_type : ChainBuilderType >-> Sortclass.
  Global Coercion builder_env : builder_type >-> Environment.
End Blockchain.

Ltac destruct_action_chain_step :=
  match goal with
  | [step: ActionChainStep _ _ |- _] =>
    destruct step as
      [?act ?acts ?new_acts ?queue_prev ?eval ?queue_new]
  end.

Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
      [?header ?queue_prev ?valid_header ?acts_from_accs ?origin_correct ?env_eq|
        ?act ?acts ?queue_prev ?queue_new ?action_trace|
        ?act ?acts ?env_eq ?queue_prev ?queue_new ?no_action_trace]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] =>
    destruct eval as
      [?limit ?origin ?from_addr ?to_addr ?amount ?enough_limit ?amount_nonnegative ?enough_balance
       ?to_addr_not_contract ?act_eq ?env_eq ?new_acts_eq |
       ?limit ?origin ?from_addr ?to_addr ?amount ?wc ?setup ?state ?enough_limit ?amount_nonnegative
        ?enough_balance ?to_addr_contract ?not_deployed
        ?act_eq ?init_some ?env_eq ?new_acts_eq |
       ?limit ?origin ?from_addr ?to_addr ?amount ?wc ?msg ?prev_state ?new_state ?resp_acts
        ?enough_limit ?amount_nonnegative ?enough_balance ?deployed ?deployed_state ?act_eq
        ?receive_some ?new_acts_eq ?env_eq ]
  end.

Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in *
  end.

Local Ltac generalize_contract_statement_aux
      bstate caddr trace is_deployed Setup Msg State Error post :=
  let P := fresh "P" in
  evar (P : forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                   (caddr : Address) (deployment_info : DeploymentInfo Setup)
                   (cstate : State) (balance : Amount)
                   (outgoing_actions_queued : list ActionBody)
                   (incoming_calls_seen : list (ContractCallInfo Msg))
                   (outgoing_txs_seen : list Tx),
           Prop);
  let H := fresh "H" in
  enough (H: exists (dep : DeploymentInfo Setup)
                    (cstate : State)
                    (inc_calls : list (ContractCallInfo Msg)),
             deployment_info Setup trace caddr = Some dep /\
             contract_state bstate caddr = Some cstate /\
             incoming_calls Msg trace caddr = Some inc_calls /\
             P (chain_height bstate)
               (current_slot bstate)
               (finalized_height bstate)
               caddr dep cstate
               (env_account_balances bstate caddr)
               (outgoing_acts bstate caddr)
               inc_calls (outgoing_txs trace caddr));
  [let depinfo := fresh "depinfo" in
   let cstate := fresh "cstate" in
   let inc_calls := fresh "inc_calls" in
   let depinfo_strong := fresh "depinfo_strong" in
   let cstate_strong := fresh "cstate_strong" in
   let inc_calls_strong := fresh "inc_calls_strong" in
   let provenP := fresh "provenP" in
   destruct H as (depinfo & cstate & inc_calls &
                  depinfo_strong & cstate_strong & inc_calls_strong & provenP);
   repeat
     match goal with
     | [|- exists _ : DeploymentInfo Setup, _] => exists depinfo
     | [|- exists _ : State, _] => exists cstate
     | [|- exists _ : list (ContractCallInfo Msg), _] => exists inc_calls
     | [|- ?a /\ ?b] => refine (conj depinfo_strong _)
     | [|- ?a /\ ?b] => refine (conj cstate_strong _)
     | [|- ?a /\ ?b] => refine (conj inc_calls_strong _)
     end;
   pattern (chain_height bstate), (current_slot bstate), (finalized_height bstate),
           caddr, depinfo, cstate, (env_account_balances bstate caddr),
           (outgoing_acts bstate caddr), inc_calls, (outgoing_txs trace caddr);
   match goal with
   | [|- ?f _ _ _ _ _ _ _ _ _ _] => instantiate (P := f); exact provenP
   end
  | post bstate caddr trace is_deployed Setup Msg State Error P ].

Local Ltac generalize_contract_statement_with_post post :=
  intros;
  match goal with
  | [bstate : ChainState, caddr : Address |- _] =>
    try
      match goal with
      | [is_reachable : reachable bstate |- _] =>
        let trace := fresh "trace" in
        destruct is_reachable as [trace]
      end;
    match goal with
      [trace : ChainTrace empty_state bstate,
               is_deployed : env_contracts (_ bstate) caddr =
                             Some (contract_to_weak_contract ?c) |- _] =>
      match type of c with
      | Contract ?Setup ?Msg ?State ?Error =>
        generalize_contract_statement_aux bstate caddr trace
                                          is_deployed Setup Msg State Error post
      end
    end
  end.

Ltac generalize_contract_statement :=
  generalize_contract_statement_with_post
    ltac:(fun _ _ _ is_deployed _ _ _ _ => revert is_deployed).

Ltac contract_induction :=
  generalize_contract_statement_with_post
    ltac:(fun bstate caddr _ is_deployed Setup Msg State Error P =>
       revert is_deployed;
       let AddBlockFacts := fresh "AddBlockFacts" in
       let DeployFacts := fresh "DeployFacts" in
       let CallFacts := fresh "CallFacts" in
       evar (AddBlockFacts :
               forall (chain_height : nat) (current_slot : nat)
                      (finalized_height : nat) (new_height : nat)
                      (new_slot : nat) (new_finalized_height : nat), Prop);
       evar (DeployFacts : forall (chain : Chain)
                                  (ctx : ContractCallContext), Prop);
       evar (CallFacts : forall (chain : Chain) (ctx : ContractCallContext)
                                (cstate : State) (outgoing_actions : list ActionBody)
                                (inc_calls : option (list (ContractCallInfo Msg))), Prop);
       apply (contract_induction _ AddBlockFacts DeployFacts CallFacts);
       cbv [P]; clear P; cycle 1; clear dependent bstate; clear dependent caddr).

Ltac solve_facts :=
  repeat match goal with
    | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ _ => Logic.True)
    | H := ?f : _ -> ContractCallContext -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ => Logic.True)
    | H := ?f : Chain -> ContractCallContext -> _ ->
    list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ => Logic.True)
    end;
    split; unset_all; subst; intros *; [
        destruct_chain_step; auto
      | destruct_action_chain_step; destruct_action_eval; auto
    ].

(* tactic for contract_induction_action_trace *)
Local Ltac generalize_contract_statement_aux_action_trace
      bstate_origin bstate caddr trace action_trace is_deployed Setup Msg State Error post :=
  let P := fresh "P" in
  evar (P : forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                   (caddr : Address) (deployment_info : DeploymentInfo Setup)
                   (cstate : State) (balance : Amount)
                   (outgoing_actions_queued : list ActionBody)
                   (incoming_calls_seen : list (ContractCallInfo Msg))
                   (outgoing_txs_seen : list Tx),
           Prop);
  let H := fresh "H" in
  enough (H: exists (dep : DeploymentInfo Setup)
                    (cstate : State)
                    (inc_calls : list (ContractCallInfo Msg)),
             deployment_info_in_action_trace Setup trace action_trace caddr = Some dep /\
             contract_state bstate caddr = Some cstate /\
             incoming_calls_in_action_trace Msg trace action_trace caddr = Some inc_calls /\
             P (chain_height bstate)
               (current_slot bstate)
               (finalized_height bstate)
               caddr dep cstate
               (env_account_balances bstate caddr)
               (outgoing_acts bstate caddr)
               inc_calls 
               (outgoing_txs_in_action_trace trace action_trace caddr)); 
  [let depinfo := fresh "depinfo" in
   let cstate := fresh "cstate" in
   let inc_calls := fresh "inc_calls" in
   let depinfo_strong := fresh "depinfo_strong" in
   let cstate_strong := fresh "cstate_strong" in
   let inc_calls_strong := fresh "inc_calls_strong" in
   let provenP := fresh "provenP" in
   destruct H as (depinfo & cstate & inc_calls &
                  depinfo_strong & cstate_strong & inc_calls_strong & provenP);
   repeat
     match goal with
     | [|- exists _ : DeploymentInfo Setup, _] => exists depinfo
     | [|- exists _ : State, _] => exists cstate
     | [|- exists _ : list (ContractCallInfo Msg), _] => exists inc_calls
     | [|- ?a /\ ?b] => refine (conj depinfo_strong _)
     | [|- ?a /\ ?b] => refine (conj cstate_strong _)
     | [|- ?a /\ ?b] => refine (conj inc_calls_strong _)
     end;
   pattern (chain_height bstate), (current_slot bstate), (finalized_height bstate),
           caddr, depinfo, cstate, (env_account_balances bstate caddr),
           (outgoing_acts bstate caddr), inc_calls, (outgoing_txs_in_action_trace trace action_trace caddr);
   match goal with
   | [|- ?f _ _ _ _ _ _ _ _ _ _] => instantiate (P := f); exact provenP
   end
  | post bstate_origin bstate caddr trace action_trace is_deployed Setup Msg State Error P ].

Local Ltac generalize_contract_statement_with_post_action_trace post :=
  intros;
  match goal with
  | [bstate_origin : ChainState, bstate : ChainState, caddr : Address |- _] =>
    
    (* try
      match goal with
      | [is_reachable : reachable bstate |- _] =>
        let trace := fresh "trace" in
        destruct is_reachable as [trace]
      end; *)
    try
      match goal with
      | [is_reachable : reachable_in_action_trace bstate_origin bstate |- _] =>
        let trace := fresh "trace" in
        let action_trace := fresh "action_trace" in
        destruct is_reachable as ([trace] & [action_trace])
      end;
    match goal with
      [trace : ChainTrace empty_state bstate_origin,
       action_trace : ActionChainTrace bstate_origin bstate,
              is_deployed : env_contracts (_ bstate) caddr =
                            Some (contract_to_weak_contract ?c) |- _] =>
      match type of c with
      | Contract ?Setup ?Msg ?State ?Error =>
        generalize_contract_statement_aux_action_trace bstate_origin bstate caddr trace action_trace
                                          is_deployed Setup Msg State Error post
      end
    end
  end.

Ltac generalize_contract_statement_action_trace :=
  generalize_contract_statement_with_post_action_trace
    ltac:(fun _ _ _ is_deployed _ _ _ _ => revert is_deployed).

Ltac contract_induction_action_trace :=
  generalize_contract_statement_with_post_action_trace
    ltac:(fun bstate_origin bstate caddr _ _ is_deployed Setup Msg State Error P =>
       revert is_deployed;
       let AddBlockFacts := fresh "AddBlockFacts" in
       let DeployFacts := fresh "DeployFacts" in
       let CallFacts := fresh "CallFacts" in
       evar (AddBlockFacts :
               forall (chain_height : nat) (current_slot : nat)
                      (finalized_height : nat) (new_height : nat)
                      (new_slot : nat) (new_finalized_height : nat), Prop);
       evar (DeployFacts : forall (chain : Chain)
                                  (ctx : ContractCallContext), Prop);
       evar (CallFacts : forall (chain : Chain) (ctx : ContractCallContext)
                                (cstate : State) (outgoing_actions : list ActionBody)
                                (inc_calls : option (list (ContractCallInfo Msg))), Prop);
       apply (contract_induction_action_trace _ AddBlockFacts DeployFacts CallFacts);
       cbv [P]; clear P; cycle 1; clear dependent bstate_origin; clear dependent bstate; clear dependent caddr).

Global Notation "'Please' 'prove' 'your' 'facts'" :=
  TagFacts (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'addition' 'of' 'a' 'block'" :=
  TagAddBlock (at level 100, only printing).
Global Notation "'Please' 'establish' 'the' 'invariant' 'after' 'deployment' 'of' 'the' 'contract'" :=
  TagDeployment (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'an' 'outgoing' 'action'" :=
  TagOutgoingAct (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'nonrecursive' 'call'" :=
  TagNonrecursiveCall (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'recursive' 'call'" :=
  TagRecursiveCall (at level 100, only printing).
Global Notation "'Please' 'prove' 'your' 'facts' 'on' 'ActionChainTrace'" :=
  TagActionTraceFacts (at level 100, only printing).

Section LiftTransactionProp.

  Context {BaseTypes : ChainBase}
          {Setup Msg State Error : Type}
         `{Serializable Setup}
         `{Serializable Msg}
         `{Serializable State}
         `{Serializable Error}.

  (** If some property [P] holds for all actions in the output of the receive function,
      the property can be lifted to all outgoing actions for all reachable states. *)
  Lemma lift_outgoing_acts_prop
          {P : ActionBody -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    reachable bstate ->
    (forall chain ctx cstate msg new_cstate acts,
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        Forall P acts) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    Forall P (outgoing_acts bstate addr).
  Proof.
    intros Hr Hc.
    contract_induction; intros; cbn in *; auto.
    - inversion_clear IH; auto.
    - apply Forall_app.
      split; auto.
      eauto.
    - apply Forall_app.
      inversion_clear IH.
      split; auto.
      eauto.
    - solve_facts.
  Qed.

  (** If the receive function always returns an empty list of actions,
  the same holds for all reachable states *)
  Lemma lift_outgoing_acts_nil
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    reachable bstate ->
    (forall chain ctx cstate msg new_cstate acts,
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        acts = []) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    outgoing_acts bstate addr = [].
  Proof.
    intros.
    enough (all_false: Forall (fun _ => False) (outgoing_acts bstate addr)) by (now destruct all_false).
    apply (lift_outgoing_acts_prop contract); auto.
    intros.
    erewrite (H4 _ _ _ _ _ acts); [constructor|eassumption].
  Qed.

  (** If some property [P] holds for all contract states in the output of the receive function,
    the property can be lifted to all contract states for all reachable states. *)
  Lemma lift_contract_state_prop
          {P : State -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address) :
    (forall chain ctx setup result,
        contract.(init) chain ctx setup = Ok result ->
        P result) ->
    (forall chain ctx cstate msg new_cstate acts,
        P cstate ->
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        P new_cstate) ->
    reachable bstate ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate addr = Some cstate
      /\ P cstate.
  Proof.
    intros Hinit Hreceive Hreach.
    contract_induction; intros; cbn in *; auto.
    - now eapply Hinit.
    - now eapply Hreceive.
    - now eapply Hreceive.
    - solve_facts.
  Qed.

  Lemma lift_dep_info_contract_state_prop
          {P : DeploymentInfo Setup -> State -> Prop}
          (contract : Contract Setup Msg State Error)
          (bstate : ChainState)
          (addr : Address)
          (trace : ChainTrace empty_state bstate) :
    (forall chain ctx setup result,
        contract.(init) chain ctx setup = Ok result ->
        P (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
          result) ->
    (forall chain ctx cstate msg new_cstate acts dep,
        P dep cstate ->
        contract.(receive) chain ctx cstate msg = Ok (new_cstate, acts) ->
        P dep new_cstate) ->
    env_contracts bstate addr = Some (contract : WeakContract) ->
    exists dep cstate,
        deployment_info Setup trace addr = Some dep /\
        contract_state bstate addr = Some cstate /\
        P dep cstate.
  Proof.
    intros Hinit Hreceive.
    contract_induction; intros; cbn in *; auto.
    - now eapply Hinit.
    - now eapply Hreceive.
    - now eapply Hreceive.
    - solve_facts.
  Qed.

End LiftTransactionProp.
