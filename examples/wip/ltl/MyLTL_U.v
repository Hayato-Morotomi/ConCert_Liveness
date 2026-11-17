From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From Stdlib Require Import ZArith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Psatz.
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
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream ChainStream.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepDetermin.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainStepSerial.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.
From ConCert.Examples.Wip.ExecutionModel Require Import MyBuildUtils.
From ConCert.Examples.Wip.ExecutionModel Require Import ActionTrace.
From ConCert.Examples.Wip.LTL Require Import MyLTLBase.
From ConCert.Examples.Wip.LTL Require Import MyLTL_G.
From ConCert.Examples.Wip.LTL Require Import MyLTLUtils.
From stdpp Require countable.
From Stdlib Require Import Relations.Relation_Definitions. (* transitive *)

Local Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
  end.

Section SolveU.
  Context {BaseTypes : ChainBase}.
  Context {Setup Msg State Error : Type}.
  Context `{ser_setup : Serializable Setup}
          `{ser_msg   : Serializable Msg}
          `{ser_state : Serializable State}
          `{ser_error : Serializable Error}.

  Definition formula := @formula BaseTypes Setup Msg State.

  Lemma solve_U
      {A : Type}
      (R : A -> A -> Prop)
      (wfR : well_founded R)
      (bot : A)
      (eq_decA : forall x y : A, {x = y} + {x <> y})
      (rank_fun : nat ->                          (* chain_height *)
                  nat ->                          (* current_slot *)
                  nat ->                          (* finalized_height *)
                  Address ->                      (* caddr *)
                  DeploymentInfo Setup ->         (* deployment_info *)
                  State ->                        (* cstate *)
                  Amount ->                       (* balance *)
                  list ActionBody ->              (* outgoing_actions_queued *)
                  list (ContractCallInfo Msg) ->  (* incoming_calls_seen *)
                  list Tx ->                      (* outgoing_txs_seen *)
                  option A)
      (contract : Contract Setup Msg State Error)
      (caddr : Address)
      (str : ChainStream)
      (start : CStr_nth 0 str = empty_state)
      (x y : formula)
    :
    forall i,
    let bstate_i := CStr_nth i str in
    let trace := CStr_clist str i in

    (
      exists v,
      let Rank_Some := fun ch cs fh caddr dep_info cstate bal out inc_calls txs =>
        rank_fun ch cs fh caddr dep_info cstate bal out inc_calls txs = Some v
      in
      satisfies contract caddr str i
        (ltl_and ltl_dep (ltl_atom Rank_Some))
    ) ->

    (
      let Not_bot := fun ch cs fh caddr dep_info cstate bal out inc_calls txs =>
        forall v1,
        rank_fun ch cs fh caddr dep_info cstate bal out inc_calls txs = Some v1 ->
        v1 <> bot
      in
      satisfies contract caddr str i
        (ltl_G (ltl_impl (ltl_atom Not_bot) x))
    ) ->

    (
      forall v1,
      let Rank_Some := fun ch cs fh caddr dep_info cstate bal out inc_calls txs =>
        rank_fun ch cs fh caddr dep_info cstate bal out inc_calls txs = Some v1 /\
        v1 <> bot
      in
      let Decrease := fun ch cs fh caddr dep_info cstate bal out inc_calls txs =>
        exists v2,
        rank_fun ch cs fh caddr dep_info cstate bal out inc_calls txs = Some v2 /\
        R v2 v1
      in
      satisfies contract caddr str i
        (ltl_G
          (ltl_impl
            (ltl_and ltl_dep (ltl_atom Rank_Some))
            (ltl_U ltl_true (ltl_atom Decrease))))
    ) ->

    (
      let Rank_Bot := fun ch cs fh caddr dep_info cstate bal out inc_calls txs =>
        rank_fun ch cs fh caddr dep_info cstate bal out inc_calls txs = Some bot
      in
      satisfies contract caddr str i
        (ltl_G (ltl_impl (ltl_atom Rank_Bot) y))
    ) ->

    satisfies contract caddr str i (ltl_U x y).
  Proof.
    intros i *. intros bstate_i trace Hstart_some Hnot_bot_x Hdec Hbot.

    set (pb_v := fun (t : nat) (v : A) =>
      env_contracts (CStr_nth t str) caddr = Some (contract : WeakContract) /\
      exists dep_info_t cstate_t inc_calls_t,
        deployment_info Setup (CStr_clist str t) caddr = Some dep_info_t /\
        contract_state (CStr_nth t str) caddr = Some cstate_t /\
        incoming_calls Msg (CStr_clist str t) caddr = Some inc_calls_t /\
        rank_fun (CStr_nth t str).(chain_height) (CStr_nth t str).(current_slot) (CStr_nth t str).(finalized_height)
          caddr dep_info_t cstate_t (env_account_balances (CStr_nth t str) caddr) (outgoing_acts (CStr_nth t str) caddr)
          inc_calls_t (outgoing_txs (CStr_clist str t) caddr) = Some v).

    assert (pb_v_dec : forall t v, pb_v t v \/ ~ pb_v t v).
    {
      intros t v. unfold pb_v.
      destruct (env_contracts (CStr_nth t str) caddr) as [wc|] eqn:Hwc;
        [|right; intros (? & _); discriminate].
      destruct (weakcontract_decidability wc (contract : WeakContract)) as [->|Hne];
        [|right; intros (Heq & _); injection Heq as Heq; congruence].
      destruct (deployment_info Setup (CStr_clist str t) caddr) as [d|] eqn:Hd;
        [|right; intros (_ & ? & ? & ? & ? & _); discriminate].
      destruct (contract_state (CStr_nth t str) caddr) as [c|] eqn:Hc;
        [|right; intros (_ & ? & ? & ? & _ & ? & _); discriminate].
      destruct (incoming_calls Msg (CStr_clist str t) caddr) as [l|] eqn:Hl;
        [|right; intros (_ & ? & ? & ? & _ & _ & ? & _); discriminate].
      destruct (rank_fun (CStr_nth t str).(chain_height) (CStr_nth t str).(current_slot) (CStr_nth t str).(finalized_height)
          caddr d c (env_account_balances (CStr_nth t str) caddr) (outgoing_acts (CStr_nth t str) caddr)
          l (outgoing_txs (CStr_clist str t) caddr)) as [r|] eqn:Hr.
      - destruct (eq_decA r v) as [->|Hrv].
        + left. split; [reflexivity|]. exists d, c, l. auto.
        + right. intros (_ & d' & c' & l' & Hd' & Hc' & Hl' & Hr').
          injection Hd' as <-. injection Hc' as <-. injection Hl' as <-. congruence.
      - right. intros (_ & d' & c' & l' & Hd' & Hc' & Hl' & Hr').
        injection Hd' as <-. injection Hc' as <-. injection Hl' as <-. congruence.
    }

    set (Rank_Some := fun v =>
      fun (ch cs fh : nat)
          (caddr0 : Address)
          (dep_info : DeploymentInfo Setup)
          (cstate : State)
          (bal : Amount)
          (out : list ActionBody)
          (inc_calls : list (ContractCallInfo Msg))
          (txs : list Tx) =>
        rank_fun ch cs fh caddr0 dep_info cstate bal out inc_calls txs = Some v).

    assert (pb_v_equiv : forall t v,
      pb_v t v <->
      satisfies contract caddr str t
        (ltl_and ltl_dep (ltl_atom (Rank_Some v)))).
    {
      intros t v. unfold pb_v, Rank_Some.
      split.
      - intros (deployed & dep_info & cstate & inc_calls & Hdep_info & Hcstate & Hinc_calls & Hrank).
        split.
        + apply (proj1
            (deployed_iff_satisfies_ltl_dep contract caddr str t)).
          exact deployed.
        + cbn [satisfies].
          intros _.
          exists dep_info, cstate, inc_calls.
          repeat split; assumption.
      - intros [Hdep Hatom].
        apply satisfies_ltl_dep_iff in Hdep.
        rename Hdep into deployed.
        cbn [satisfies] in Hatom.
        destruct_deployed_typed.
        split; [exact deployed|].
        exists dep_info0, cstate0, inc_calls0.
        repeat split; assumption.
    }

    set (Decrease := fun v1 =>
      fun ch cs fh caddr0 dep_info cstate
          (bal : Amount) (out : list ActionBody) inc_calls (txs : list Tx) =>
        exists v2,
        rank_fun ch cs fh caddr0 dep_info cstate bal out inc_calls txs = Some v2 /\
        R v2 v1).

    assert (Decrease_equiv : forall t v1,
      satisfies contract caddr str t (ltl_atom (Decrease v1)) ->
      env_contracts (CStr_nth t str) caddr = Some (contract : WeakContract) ->
      exists v2, pb_v t v2 /\ R v2 v1).
    {
      intros t v1 Hatom deployed.
      cbn [satisfies] in Hatom.
      destruct_deployed_typed.
      unfold Decrease in H.
      destruct H as (v2 & Hrank & HR).
      exists v2. split; [|exact HR].
      apply (proj2 (pb_v_equiv t v2)).
      split.
      - apply (proj1
          (deployed_iff_satisfies_ltl_dep contract caddr str t)).
        exact deployed.
      - cbn [satisfies].
        intros _.
        exists dep_info0, cstate0, inc_calls0.
        repeat split; assumption.
    }

    set (ReachBot := fun (v : A) =>
      forall j, (i <= j)%nat -> pb_v j v ->
        exists k, (j <= k)%nat /\ pb_v k bot).

    assert (HReachBot : forall v, ReachBot v).
    {
      intro v.
      apply (well_founded_induction wfR (fun v => ReachBot v)).
      clear v. intros v1 IH j Hij Hpb_j.
      destruct (eq_decA v1 bot) as [->|Hneq].
      - exists j. split; [lia|exact Hpb_j].
      - specialize (Hdec v1).
        cbn [satisfies] in Hdec.
        specialize (Hdec j Hij).
        assert (Hpre :
          satisfies contract caddr str j
            (ltl_and ltl_dep
              (ltl_atom
                (fun ch cs fh caddr0 dep_info cstate bal out inc_calls txs =>
                  rank_fun ch cs fh caddr0
                    dep_info cstate bal out inc_calls txs = Some v1 /\
                  v1 <> bot)))).
        {
          pose proof (proj1 (pb_v_equiv j v1) Hpb_j) as Hpb_sat.
          destruct Hpb_sat as [Hdep Hatom].
          split; [exact Hdep|].
          pose proof Hdep as deployed_j.
          apply satisfies_ltl_dep_iff in deployed_j.
          cbn [satisfies] in Hatom |- *.
          destruct_deployed_typed.
          intros _.
          exists dep_info0, cstate0, inc_calls0.
          repeat split; auto.
        }
        specialize (Hdec Hpre).
        cbn [satisfies] in Hdec.
        destruct Hdec as (m & Hjm & _ & Hdec_atom).

        pose proof (proj1 (pb_v_equiv j v1) Hpb_j) as Hpb_sat.
        destruct Hpb_sat as [Hdep_j _].
        apply satisfies_ltl_dep_iff in Hdep_j.
        assert (deployed_m :
          env_contracts (CStr_nth m str) caddr =
            Some (contract : WeakContract)).
        { eapply CStr_wc_preserve; eauto. }

        destruct (Decrease_equiv m v1 Hdec_atom deployed_m)
          as (v2 & Hpb_m & HR).
        assert (Him : (i <= m)%nat) by lia.
        specialize (IH v2 HR m Him Hpb_m).
        destruct IH as (k & Hmk & Hpb_k).
        exists k. split; [lia|exact Hpb_k].
    }

    destruct Hstart_some as (v0 & Hstart_sat).
    assert (Hpb_i : pb_v i v0).
    { apply (proj2 (pb_v_equiv i v0)). exact Hstart_sat. }
    specialize (HReachBot v0 i (le_n i) Hpb_i).
    destruct HReachBot as (K & HiK & Hpb_K).

    set (pb := fun t => pb_v t bot).
    assert (Hpb_dec : forall t, pb t \/ ~ pb t).
    { intros t. apply pb_v_dec. }

    assert (Hex_first :
      exists m,
        pb m /\
        (i <= m <= K)%nat /\
        (forall j, (i <= j < m)%nat -> ~ pb j)).
    {
      clear - HiK Hpb_K Hpb_dec.
      assert (Hlem : forall n,
        (i <= n <= K)%nat ->
        (forall j, (i <= j < n)%nat -> ~ pb j) ->
        exists m,
          pb m /\
          (i <= m <= K)%nat /\
          forall j, (i <= j < m)%nat -> ~ pb j).
      {
        intros n.
        remember (K - n)%nat as d.
        generalize dependent n.
        induction d as [|d IHd].
        - intros n Heq Hle Hnot.
          assert (n = K) by lia. subst n.
          exists K. split; [exact Hpb_K|].
          split; [lia|exact Hnot].
        - intros n Heq Hle Hnot.
          destruct (Hpb_dec n) as [Hpb_n|Hnot_pb_n].
          + exists n. split; [exact Hpb_n|].
            split; [lia|exact Hnot].
          + apply IHd with (n := S n).
            * lia.
            * lia.
            * intros j Hj.
              assert (j < n \/ j = n)%nat by lia.
              destruct H as [Hlt|]; [|subst; auto].
              apply Hnot; lia.
      }
      apply Hlem with (n := i).
      - lia.
      - intros j Hj. lia.
    }

    destruct Hex_first as (m & Hpb_m & Him_K & Hnot_pb).
    exists m.
    split; [lia|].
    split.
    - intros j Hj1 Hj2.
      specialize (Hnot_bot_x j ltac:(lia)).
      cbn [satisfies] in Hnot_bot_x.
      apply Hnot_bot_x.
      cbn [satisfies].
      intros deployed_j.
      cstr_destruct_deployed_typed.
      exists dep_info, cstate, inc_calls.
      repeat split; try assumption.
      intros v1 Hrank Heq.
      subst v1.
      specialize (Hnot_pb j ltac:(lia)).
      apply Hnot_pb.
      unfold pb, pb_v.
      split; [exact deployed_j|].
      exists dep_info, cstate, inc_calls.
      repeat split; assumption.

    - specialize (Hbot m ltac:(lia)).
      cbn [satisfies] in Hbot.
      apply Hbot.
      pose proof (proj1 (pb_v_equiv m bot) Hpb_m) as Hpb_sat.
      destruct Hpb_sat as [_ Hrank_bot].
      exact Hrank_bot.
  Qed.

  Record CallSpec := {
    origin_addr_spec : Address -> Prop;
    amount_spec      : Amount  -> Prop;
    msg_spec         : option Msg -> Prop;
  }.

  Definition call_queued
      (s : CallSpec) (min_limit : nat)
      (caddr : Address) (st : ChainState) : Prop :=
    exists limit origin_addr amount msg,
      (min_limit <= limit)%nat /\
      origin_addr_spec s origin_addr /\
      amount_spec s amount /\
      msg_spec s msg /\
      List.In (build_act limit origin_addr origin_addr
                (match msg with
                 | None => act_transfer caddr amount
                 | Some m => act_call caddr amount ((@serialize Msg _) m)
                 end))
              st.(chain_state_queue).

  Definition call_infinitely_often
      (s : CallSpec) (min_limit : nat)
      (caddr : Address) (str : ChainStream) : Prop :=
    forall n, exists m,
      call_queued s min_limit caddr (CStr_nth (n + m) str).

  Inductive TagCallDoNotIncrease := tag_call_donot_increase.
  Inductive TagCallDecrease := tag_call_decrease.
  Inductive TagAddBlockDoNotIncrease := tag_add_block_donot_increase.

  Inductive TagOutgoingActDoNotIncrease := tag_outgoing_act_donot_increase.
  Inductive TagNonrecursiveCallDoNotIncrease := tag_nonrecursive_call_donot_increase.
  Inductive TagRecursiveCallDoNotIncrease := tag_recursive_call_donot_increase.

  Hint Constructors
    TagCallDoNotIncrease TagCallDecrease TagAddBlockDoNotIncrease
    TagOutgoingActDoNotIncrease TagNonrecursiveCallDoNotIncrease TagRecursiveCallDoNotIncrease : core.

  Inductive TagAddBlockDecrease := tag_add_block_decrease.

  Hint Constructors TagAddBlockDecrease  : core.

  Section RankStep.
  Context {A : Type} (R : A -> A -> Prop) (bot : A).

  Definition le_R (v2 v1 : A) : Prop := R v2 v1 \/ v1 = v2.
  Definition rank_le (o : option A) (v1 : A) : Prop :=
    match o with Some v2 => le_R v2 v1 | None => False end.
  Definition rank_lt (o : option A) (v1 : A) : Prop :=
    match o with Some v2 => R v2 v1 | None => False end.

  Lemma rank_le_refl v : rank_le (Some v) v.
  Proof. right. reflexivity. Qed.

  Variable rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                      Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A.
  Variable contract : Contract Setup Msg State Error.
  Variable caddr : Address.

  Lemma rank_step
      (QB : option A -> A -> Prop)
      (add_block_case :
        forall v1 h s f h' s' f' dep cst bal inc txs
               (valid_height : h' = S h) (valid_slot : s < s') (valid_finalized : f <= f' /\ f' < h')
               (prev_rank : rank_fun h s f caddr dep cst bal [] inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagAddBlockDoNotIncrease),
          QB (rank_fun h' s' f' caddr dep cst bal [] inc txs) v1)
      (outgoing_act_case :
        forall v1 h s f dep cst bal out_act out_acts inc txs tx
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
               (prev_rank : rank_fun h s f caddr dep cst bal (out_act :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagOutgoingActDoNotIncrease),
          rank_le (rank_fun h s f caddr dep cst (bal - act_body_amount out_act)%Z out_acts inc (tx :: txs)) v1)
      (nonrecursive_call_case :
        forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_other : ctx_from ctx <> caddr)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagNonrecursiveCallDoNotIncrease),
          rank_le (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1)
      (recursive_call_case :
        forall v1 chain dep cst head out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_self : ctx_from ctx = caddr)
               (action_facts :
                 match head with
                 | act_transfer to amount => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\ msg = None
                 | act_call to amount msg_ser => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\
                                                 msg <> None /\ deserialize msg_ser = msg
                 | _ => False
                 end)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx) (head :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagRecursiveCallDoNotIncrease),
          rank_le (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     (build_tx (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_contract_address ctx) (ctx_amount ctx)
                        (tx_call (match head with act_call _ _ m => Some m | _ => None end)) :: txs)) v1)
      {from : ChainState} (mid to : ChainState) (trace : ChainTrace from mid) (reach : reachable mid)
      (step : ChainStep mid to)
      (v1 : A) dep cst inc :
    env_contracts mid caddr = Some (contract : WeakContract) ->
    deployment_info Setup trace caddr = Some dep ->
    contract_state mid caddr = Some cst ->
    incoming_calls Msg trace caddr = Some inc ->
    rank_fun (chain_height mid) (current_slot mid) (finalized_height mid) caddr dep cst
      (env_account_balances mid caddr) (outgoing_acts mid caddr) inc (outgoing_txs trace caddr) = Some v1 ->
    v1 <> bot ->
    exists dep' cst' inc',
      deployment_info Setup (snoc trace step) caddr = Some dep' /\
      contract_state to caddr = Some cst' /\
      incoming_calls Msg (snoc trace step) caddr = Some inc' /\
      let r := rank_fun (chain_height to) (current_slot to) (finalized_height to) caddr dep' cst'
                 (env_account_balances to caddr) (outgoing_acts to caddr) inc' (outgoing_txs (snoc trace step) caddr) in
      (chain_state_queue mid = [] /\ QB r v1) \/
      (chain_state_queue mid <> [] /\ rank_le r v1).
  Proof.
    intros deployed Hdep Hcst Hinc Hrank not_bot.
    assert (is_contract : address_is_contract caddr = true)
      by (eapply contract_addr_format; eauto).
    destruct_chain_step.
    - (* block *)
      cbn in *.
      exists dep, cst, inc.
      rewrite env_eq. cbn.
      destruct valid_header as [Hh Hs Hf Hcreator Hreward].
      repeat split; auto.
      left. split; [exact queue_prev|].
      destruct (address_eqb_spec caddr (block_creator header)) as [Heq|Hne].
      { rewrite <- Heq in Hcreator. congruence. }
      rewrite outgoing_acts_after_block_nil by auto.
      unfold outgoing_acts in Hrank. rewrite queue_prev in Hrank. cbn in Hrank.
      fold (outgoing_txs trace caddr).
      eapply add_block_case; eauto; try lia; try constructor.
    - (* user action *)
      destruct_action_eval; cbn in *.
      + (* transfer *)
        exists dep, cst, inc.
        rewrite env_eq; cbn.
        repeat split; try assumption.
        right. split; [try rewrite queue_prev; discriminate|].
        destruct (address_eqb_spec caddr to_addr) as [->|Hto]; [congruence|].
        unfold outgoing_acts in *. rewrite queue_prev, queue_new, new_acts_eq in *. subst act. cbn in *.
        rewrite (address_eq_sym from_addr caddr) in *.
        destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
        * cbn in *.
          replace (- amount + env_account_balances mid caddr)%Z
            with (env_account_balances mid caddr - act_body_amount (act_transfer to_addr amount))%Z
            by (cbn; lia).
          fold (outgoing_txs trace caddr) in *.
          eapply outgoing_act_case; eauto; cbn; auto; try constructor.
        * rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
          cbn in *. fold (outgoing_txs trace caddr) in *.
          rewrite Hrank. apply rank_le_refl.
      + (* deploy *)
        assert (Hne : to_addr <> caddr) by (intro; subst; congruence).
        rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) in * by auto.
        exists dep, cst, inc.
        rewrite env_eq; cbn.
        rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) by auto.
        repeat split; try assumption.
        right. split; [try rewrite queue_prev; discriminate|].
        unfold outgoing_acts in *. rewrite queue_prev, queue_new, new_acts_eq in *. subst act. cbn in *.
        rewrite (address_eq_sym from_addr caddr) in *.
        destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
        * cbn in *.
          replace (- amount + env_account_balances mid caddr)%Z
            with (env_account_balances mid caddr - act_body_amount (act_deploy amount wc setup))%Z
            by (cbn; lia).
          fold (outgoing_txs trace caddr) in *.
          eapply outgoing_act_case; eauto; cbn; auto; try constructor.
        * rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
          cbn in *. fold (outgoing_txs trace caddr) in *.
          rewrite Hrank. apply rank_le_refl.
      + (* call *)
        unfold outgoing_acts in *. rewrite queue_prev, queue_new in *. subst act new_acts. cbn in *.
        rewrite filter_app, filter_map, map_app, map_map in *; cbn in *.
        destruct (address_eqb_spec to_addr caddr) as [->|Hto].
        * (* call to caddr *)
          replace wc with (contract : WeakContract) in * by congruence.
          destruct (wc_receive_strong ltac:(eassumption))
            as (prev_state_strong & msg_strong & resp_state_strong &
                deser_state & deser_msg & <- & receive).
          unfold contract_state in Hcst. rewrite deployed_state in Hcst. cbn in Hcst.
          replace prev_state_strong with cst in * by congruence.
          assert (Hbal_to : env_account_balances to caddr =
                    (if (caddr =? from_addr)%address
                     then env_account_balances mid caddr
                     else amount + env_account_balances mid caddr)%Z).
          { rewrite env_eq; cbn. rewrite address_eq_refl.
            destruct (address_eqb_spec caddr from_addr); cbn; lia. }
          exists dep, resp_state_strong, (build_call_info limit origin from_addr amount msg_strong :: inc).
          rewrite env_eq; cbn.
          rewrite address_eq_refl; cbn.
          rewrite deserialize_serialize.
          rewrite Hinc.
          split; [assumption|]. split; [reflexivity|]. split.
          { destruct msg_strong as [ms|], msg as [m|]; cbn in *; try congruence.
            now replace (deserialize m) with (Some ms) by auto. }
          right. split; [try rewrite queue_prev; discriminate|].
          rewrite filter_true, map_id.
          fold (outgoing_txs trace caddr) in *.
          destruct (address_eqb_spec from_addr caddr) as [->|Hfrom].
          -- (* recursive call *)
             rewrite address_eq_refl in *. cbn in *.
             replace (- amount + (amount + env_account_balances mid caddr))%Z
               with (env_account_balances to caddr) by lia.
             rewrite <- Hbal_to in Hrank.
             destruct msg_strong as [ms|], msg as [m|]; cbn in *; try congruence.
             ++ eapply (recursive_call_case v1 (transfer_balance caddr caddr amount mid) dep cst
                          (act_call caddr amount m) _ inc _
                          (build_ctx limit origin caddr caddr (env_account_balances to caddr) amount) (Some ms));
                  cbn; eauto; try constructor.
             ++ eapply (recursive_call_case v1 (transfer_balance caddr caddr amount mid) dep cst
                          (act_transfer caddr amount) _ inc _
                          (build_ctx limit origin caddr caddr (env_account_balances to caddr) amount) None);
                  cbn; eauto; try constructor.
          -- (* nonrecursive call *)
             rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
             cbn in *.
             replace (amount + env_account_balances mid caddr)%Z with (env_account_balances to caddr) by lia.
             replace (env_account_balances mid caddr)
               with (env_account_balances to caddr - amount)%Z in Hrank by lia.
             eapply (nonrecursive_call_case v1 (transfer_balance from_addr caddr amount mid) dep cst
                       _ inc _
                       (build_ctx limit origin from_addr caddr (env_account_balances to caddr) amount) msg_strong);
               cbn; eauto; try constructor.
        * (* call to other contract *)
          exists dep, cst, inc.
          rewrite env_eq; cbn.
          rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) by auto.
          rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) in * by auto.
          repeat split; try assumption.
          right. split; [try rewrite queue_prev; discriminate|].
          rewrite filter_false. cbn.
          fold (outgoing_txs trace caddr) in *.
          rewrite (address_eq_sym from_addr caddr) in *.
          destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
          -- (* call from caddr to another contract *)
             rewrite ?address_eq_refl in *. cbn in *.
             destruct msg as [m|].
             ++ replace (- amount + env_account_balances mid caddr)%Z
                  with (env_account_balances mid caddr - act_body_amount (act_call to_addr amount m))%Z
                  by (cbn; lia).
                eapply outgoing_act_case; eauto; cbn; auto; try constructor.
             ++ replace (- amount + env_account_balances mid caddr)%Z
                  with (env_account_balances mid caddr - act_body_amount (act_transfer to_addr amount))%Z
                  by (cbn; lia).
                eapply outgoing_act_case; eauto; cbn; auto; try constructor.
          -- rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
             cbn in *.
             rewrite Hrank. apply rank_le_refl.
    - (* contract action *)
      destruct_action_eval; cbn in *.
      + (* transfer *)
        exists dep, cst, inc.
        rewrite env_eq; cbn.
        repeat split; try assumption.
        right. split; [try rewrite queue_prev; discriminate|].
        destruct (address_eqb_spec caddr to_addr) as [->|Hto]; [congruence|].
        unfold outgoing_acts in *. rewrite queue_prev, queue_new, new_acts_eq in *. subst act. cbn in *.
        rewrite (address_eq_sym from_addr caddr) in *.
        destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
        * cbn in *.
          replace (- amount + env_account_balances mid caddr)%Z
            with (env_account_balances mid caddr - act_body_amount (act_transfer to_addr amount))%Z
            by (cbn; lia).
          fold (outgoing_txs trace caddr) in *.
          eapply outgoing_act_case; eauto; cbn; auto; try constructor.
        * rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
          cbn in *. fold (outgoing_txs trace caddr) in *.
          rewrite Hrank. apply rank_le_refl.
      + (* deploy *)
        assert (Hne : to_addr <> caddr) by (intro; subst; congruence).
        rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) in * by auto.
        exists dep, cst, inc.
        rewrite env_eq; cbn.
        rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) by auto.
        repeat split; try assumption.
        right. split; [try rewrite queue_prev; discriminate|].
        unfold outgoing_acts in *. rewrite queue_prev, queue_new, new_acts_eq in *. subst act. cbn in *.
        rewrite (address_eq_sym from_addr caddr) in *.
        destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
        * cbn in *.
          replace (- amount + env_account_balances mid caddr)%Z
            with (env_account_balances mid caddr - act_body_amount (act_deploy amount wc setup))%Z
            by (cbn; lia).
          fold (outgoing_txs trace caddr) in *.
          eapply outgoing_act_case; eauto; cbn; auto; try constructor.
        * rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
          cbn in *. fold (outgoing_txs trace caddr) in *.
          rewrite Hrank. apply rank_le_refl.
      + (* call *)
        unfold outgoing_acts in *. rewrite queue_prev, queue_new in *. subst act new_acts. cbn in *.
        rewrite filter_app, filter_map, map_app, map_map in *; cbn in *.
        destruct (address_eqb_spec to_addr caddr) as [->|Hto].
        * (* call to caddr *)
          replace wc with (contract : WeakContract) in * by congruence.
          destruct (wc_receive_strong ltac:(eassumption))
            as (prev_state_strong & msg_strong & resp_state_strong &
                deser_state & deser_msg & <- & receive).
          unfold contract_state in Hcst. rewrite deployed_state in Hcst. cbn in Hcst.
          replace prev_state_strong with cst in * by congruence.
          assert (Hbal_to : env_account_balances to caddr =
                    (if (caddr =? from_addr)%address
                     then env_account_balances mid caddr
                     else amount + env_account_balances mid caddr)%Z).
          { rewrite env_eq; cbn. rewrite address_eq_refl.
            destruct (address_eqb_spec caddr from_addr); cbn; lia. }
          exists dep, resp_state_strong, (build_call_info limit origin from_addr amount msg_strong :: inc).
          rewrite env_eq; cbn.
          rewrite address_eq_refl; cbn.
          rewrite deserialize_serialize.
          rewrite Hinc.
          split; [assumption|]. split; [reflexivity|]. split.
          { destruct msg_strong as [ms|], msg as [m|]; cbn in *; try congruence.
            now replace (deserialize m) with (Some ms) by auto. }
          right. split; [try rewrite queue_prev; discriminate|].
          rewrite filter_true, map_id.
          fold (outgoing_txs trace caddr) in *.
          destruct (address_eqb_spec from_addr caddr) as [->|Hfrom].
          -- (* recursive call *)
             rewrite address_eq_refl in *. cbn in *.
             replace (- amount + (amount + env_account_balances mid caddr))%Z
               with (env_account_balances to caddr) by lia.
             rewrite <- Hbal_to in Hrank.
             destruct msg_strong as [ms|], msg as [m|]; cbn in *; try congruence.
             ++ eapply (recursive_call_case v1 (transfer_balance caddr caddr amount mid) dep cst
                          (act_call caddr amount m) _ inc _
                          (build_ctx limit origin caddr caddr (env_account_balances to caddr) amount) (Some ms));
                  cbn; eauto; try constructor.
             ++ eapply (recursive_call_case v1 (transfer_balance caddr caddr amount mid) dep cst
                          (act_transfer caddr amount) _ inc _
                          (build_ctx limit origin caddr caddr (env_account_balances to caddr) amount) None);
                  cbn; eauto; try constructor.
          -- (* nonrecursive call *)
             rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
             cbn in *.
             replace (amount + env_account_balances mid caddr)%Z with (env_account_balances to caddr) by lia.
             replace (env_account_balances mid caddr)
               with (env_account_balances to caddr - amount)%Z in Hrank by lia.
             eapply (nonrecursive_call_case v1 (transfer_balance from_addr caddr amount mid) dep cst
                       _ inc _
                       (build_ctx limit origin from_addr caddr (env_account_balances to caddr) amount) msg_strong);
               cbn; eauto; try constructor.
        * (* call to other contract *)
          exists dep, cst, inc.
          rewrite env_eq; cbn.
          rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) by auto.
          rewrite ?(address_eq_ne to_addr caddr), ?(address_eq_ne caddr to_addr) in * by auto.
          repeat split; try assumption.
          right. split; [try rewrite queue_prev; discriminate|].
          rewrite filter_false. cbn.
          fold (outgoing_txs trace caddr) in *.
          rewrite (address_eq_sym from_addr caddr) in *.
          destruct (address_eqb_spec caddr from_addr) as [<-|Hfrom].
          -- (* call from caddr to another contract *)
             rewrite ?address_eq_refl in *. cbn in *.
             destruct msg as [m|].
             ++ replace (- amount + env_account_balances mid caddr)%Z
                  with (env_account_balances mid caddr - act_body_amount (act_call to_addr amount m))%Z
                  by (cbn; lia).
                eapply outgoing_act_case; eauto; cbn; auto; try constructor.
             ++ replace (- amount + env_account_balances mid caddr)%Z
                  with (env_account_balances mid caddr - act_body_amount (act_transfer to_addr amount))%Z
                  by (cbn; lia).
                eapply outgoing_act_case; eauto; cbn; auto; try constructor.
          -- rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
             cbn in *.
             rewrite Hrank. apply rank_le_refl.
    -
      exists dep, cst, inc.
      cbn.
      rewrite env_eq.
      repeat split; try assumption.
      right. split; [try rewrite queue_prev; discriminate|].
      assert (outgoing_acts_eq : outgoing_acts mid caddr = outgoing_acts to caddr).
      { unfold outgoing_acts.
        rewrite queue_new, queue_prev.
        cbn.
        unfold act_is_from_account in *.
        destruct_address_eq; congruence. }
      rewrite <- outgoing_acts_eq.
      fold (outgoing_txs trace caddr).
      rewrite Hrank. apply rank_le_refl.
  Qed.
  End RankStep.

  Definition RankAt {A : Type}
      (rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                  Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A)
      (caddr : Address) (str : ChainStream) (n : nat) (v : A) : Prop :=
    exists d c l,
      deployment_info Setup (CStr_clist str n) caddr = Some d /\
      contract_state (CStr_nth n str) caddr = Some c /\
      incoming_calls Msg (CStr_clist str n) caddr = Some l /\
      rank_fun (chain_height (CStr_nth n str)) (current_slot (CStr_nth n str))
        (finalized_height (CStr_nth n str)) caddr d c
        (env_account_balances (CStr_nth n str) caddr) (outgoing_acts (CStr_nth n str) caddr)
        l (outgoing_txs (CStr_clist str n) caddr) = Some v.

  Lemma le_R_trans {A} (R : A -> A -> Prop) (transR : transitive A R) v1 v2 v3 :
    le_R R v3 v2 -> le_R R v2 v1 -> le_R R v3 v1.
  Proof.
    unfold le_R. intros [H32|H32] [H21|H21]; subst; auto.
    left. eapply transR; eauto.
  Qed.

  Lemma rank_lt_le {A} (R : A -> A -> Prop) o v : rank_lt R o v -> rank_le R o v.
  Proof. destruct o; cbn; auto. intros; left; auto. Qed.

  Lemma solve_U_eventually_decrease
        (contract : Contract Setup Msg State Error)
        {A : Type}
        (R : A -> A -> Prop)
        (wfR : well_founded R)
        (transR : transitive A R)
        (bot : A)
        (eq_decA : forall x y : A, {x = y} + {x <> y})
        (rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                    Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A)
        (caddr : Address)
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        (i : nat)
        (initial_dep_info : DeploymentInfo Setup) :
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract) ->
    deployment_info Setup (CStr_clist str i) caddr = Some initial_dep_info ->
    (exists v,
      satisfies contract caddr str i
        (ltl_atom (fun ch cs fh a dep cst bal out inc txs =>
                     rank_fun ch cs fh a dep cst bal out inc txs = Some v))) ->
    (* add_block_case *)
    (forall v1 h s f h' s' f' dep cst bal inc txs
               (valid_height : h' = S h) (valid_slot : s < s') (valid_finalized : f <= f' /\ f' < h')
               (prev_rank : rank_fun h s f caddr dep cst bal [] inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagAddBlockDecrease),
          rank_lt R (rank_fun h' s' f' caddr dep cst bal [] inc txs) v1) ->
    (* outgoing_act_case *)
    (forall v1 h s f dep cst bal out_act out_acts inc txs tx
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
               (prev_rank : rank_fun h s f caddr dep cst bal (out_act :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagOutgoingActDoNotIncrease),
          rank_le R (rank_fun h s f caddr dep cst (bal - act_body_amount out_act)%Z out_acts inc (tx :: txs)) v1) ->
    (* nonrecursive_call_case *)
    (forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_other : ctx_from ctx <> caddr)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagNonrecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1) ->
    (* recursive_call_case *)
    (forall v1 chain dep cst head out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_self : ctx_from ctx = caddr)
               (action_facts :
                 match head with
                 | act_transfer to amount => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\ msg = None
                 | act_call to amount msg_ser => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\
                                                 msg <> None /\ deserialize msg_ser = msg
                 | _ => False
                 end)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx) (head :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagRecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     (build_tx (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_contract_address ctx) (ctx_amount ctx)
                        (tx_call (match head with act_call _ _ m => Some m | _ => None end)) :: txs)) v1) ->
    forall v1,
      let Rank_Some := fun ch cs fh a dep cst bal out inc txs =>
        rank_fun ch cs fh a dep cst bal out inc txs = Some v1 /\ v1 <> bot in
      let Decrease := fun ch cs fh a dep cst bal out inc txs =>
        exists v2, rank_fun ch cs fh a dep cst bal out inc txs = Some v2 /\ R v2 v1 in
      satisfies contract caddr str i
        (ltl_G (ltl_impl (ltl_and ltl_dep (ltl_atom Rank_Some))
                         (ltl_U ltl_true (ltl_atom Decrease)))).
  Proof.
    intros deployed_i Hdep_i Hrank_i add_block_case outgoing_act_case
      nonrecursive_call_case recursive_call_case v1 Rank_Some Decrease.
    cbn [satisfies]. intros j Hij [Hdep_j Hatom_j].
    apply satisfies_ltl_dep_iff in Hdep_j. rename Hdep_j into deployed_j.
    cbn [satisfies] in Hatom_j.
    destruct (Hatom_j deployed_j) as (d_j & c_j & l_j & Hd_j & Hc_j & Hl_j & Hr_j & Hnb).

    assert (step : forall n v, (j <= n)%nat -> RankAt rank_fun caddr str n v -> v <> bot ->
      exists v', RankAt rank_fun caddr str (S n) v' /\
        ((chain_state_queue (CStr_nth n str) = [] /\ R v' v) \/
         (chain_state_queue (CStr_nth n str) <> [] /\ le_R R v' v))).
    { intros n v Hjn (d & c & l & Hd & Hc & Hl & Hr) Hnb_v.
      pose proof (CStr_wc_preserve str deployed_j n Hjn) as deployed_n.
      destruct (rank_step R bot rank_fun contract caddr (rank_lt R)
                  (fun v1 h s f h' s' f' dep cst bal inc txs Hh Hs Hf Hp Hn _ =>
                     add_block_case v1 h s f h' s' f' dep cst bal inc txs Hh Hs Hf Hp Hn
                       tag_add_block_decrease)
                  outgoing_act_case nonrecursive_call_case recursive_call_case
                  (CStr_nth n str) (CStr_nth (S n) str) (CStr_clist str n)
                  (CStr_nth_reachable str start n) (CStr_link str n) v d c l
                  deployed_n Hd Hc Hl Hr Hnb_v)
        as (d' & c' & l' & Hd' & Hc' & Hl' & Hcase).
      rewrite <- CStr_clist_snoc in Hd', Hl', Hcase.
      cbv zeta in Hcase.
      match type of Hcase with
      | context [rank_fun ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
          destruct (rank_fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [v'|] eqn:Hr'
      end.
      - exists v'. split.
        + exists d', c', l'. repeat split; assumption.
        + destruct Hcase as [(Hq & Hlt) | (Hq & Hle)]; [left | right]; split; assumption.
      - destruct Hcase as [(_ & []) | (_ & [])]. }

    assert (dec_intro : forall k v2, RankAt rank_fun caddr str k v2 -> R v2 v1 ->
      satisfies contract caddr str k (ltl_atom Decrease)).
    { intros k v2 (d & c & l & Hd & Hc & Hl & Hr) HR.
      cbn [satisfies]. intros _. exists d, c, l. repeat split; try assumption.
      exists v2. split; assumption. }
    assert (rank_le_or_dec : forall a, (j <= a)%nat ->
      (exists v, RankAt rank_fun caddr str a v /\ le_R R v v1) \/
      (exists k, (j <= k)%nat /\ satisfies contract caddr str k (ltl_atom Decrease))).
    { intros a Hja.
      remember (a - j)%nat as dd eqn:Hdd. generalize dependent a.
      induction dd as [|dd IH]; intros a Hdd Hja.
      - assert (a = j) by lia. subst a. left. exists v1. split.
        + exists d_j, c_j, l_j. repeat split; assumption.
        + right. reflexivity.
      - destruct a as [|a']; [lia|].
        destruct (IH a' ltac:(lia) ltac:(lia)) as [(v & Hra & Hle) | Hdec]; [|right; exact Hdec].
        destruct (eq_decA v bot) as [-> | Hnb_v].
        + right. exists a'. split; [lia|]. apply (dec_intro a' bot Hra).
          destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq].
        + destruct (step a' v ltac:(lia) Hra Hnb_v) as (v' & Hra' & Hcase).
          left. exists v'. split; [exact Hra'|].
          destruct Hcase as [(_ & HR) | (_ & Hle')].
          * eapply le_R_trans; [exact transR | left; exact HR | exact Hle].
          * eapply le_R_trans; eauto. }

    destruct (cstr_queue_empties str start (chain_state_queue (CStr_nth j str)) j eq_refl)
      as (n & Hjn & Hq_n).
    assert (Hfinal : exists k, (j <= k)%nat /\ satisfies contract caddr str k (ltl_atom Decrease)).
    { destruct (rank_le_or_dec n Hjn) as [(v & Hra & Hle) | Hdec]; [|exact Hdec].
      destruct (eq_decA v bot) as [-> | Hnb_v].
      - exists n. split; [lia|]. apply (dec_intro n bot Hra).
        destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq].
      - destruct (step n v Hjn Hra Hnb_v) as (v' & Hra' & Hcase).
        exists (S n). split; [lia|]. apply (dec_intro (S n) v' Hra').
        destruct Hcase as [(_ & HR) | (Hq & _)]; [|congruence].
        destruct Hle as [HR1 | <-]; [eapply transR; eauto | exact HR]. }
    destruct Hfinal as (k & Hjk & Hdec).
    exists k. split; [lia|]. split; [intros; exact I|]. exact Hdec.
  Qed.

  Lemma solve_U_eventually_decrease_spec
        (contract : Contract Setup Msg State Error)
        {A : Type}
        (R : A -> A -> Prop)
        (wfR : well_founded R)
        (transR : transitive A R)
        (bot : A)
        (eq_decA : forall x y : A, {x = y} + {x <> y})
        (rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                    Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A)
        (caddr : Address)
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        (i : nat)
        (initial_dep_info : DeploymentInfo Setup)
        (s : CallSpec) :
    (forall min_limit, call_infinitely_often s min_limit caddr str) ->
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract) ->
    deployment_info Setup (CStr_clist str i) caddr = Some initial_dep_info ->
    (exists v,
      satisfies contract caddr str i
        (ltl_atom (fun ch cs fh a dep cst bal out inc txs =>
                     rank_fun ch cs fh a dep cst bal out inc txs = Some v))) ->
    (* add_block_case *)
    (forall v1 h s f h' s' f' dep cst bal inc txs
               (valid_height : h' = S h) (valid_slot : s < s') (valid_finalized : f <= f' /\ f' < h')
               (prev_rank : rank_fun h s f caddr dep cst bal [] inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagAddBlockDoNotIncrease),
          rank_le R (rank_fun h' s' f' caddr dep cst bal [] inc txs) v1) ->
    (* outgoing_act_case *)
    (forall v1 h s f dep cst bal out_act out_acts inc txs tx
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
               (prev_rank : rank_fun h s f caddr dep cst bal (out_act :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagOutgoingActDoNotIncrease),
          rank_le R (rank_fun h s f caddr dep cst (bal - act_body_amount out_act)%Z out_acts inc (tx :: txs)) v1) ->
    (* nonrecursive_call_case *)
    (forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_other : ctx_from ctx <> caddr)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagNonrecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1) ->
    (* recursive_call_case *)
    (forall v1 chain dep cst head out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_self : ctx_from ctx = caddr)
               (action_facts :
                 match head with
                 | act_transfer to amount => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\ msg = None
                 | act_call to amount msg_ser => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\
                                                 msg <> None /\ deserialize msg_ser = msg
                 | _ => False
                 end)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx) (head :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagRecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     (build_tx (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_contract_address ctx) (ctx_amount ctx)
                        (tx_call (match head with act_call _ _ m => Some m | _ => None end)) :: txs)) v1) ->

    (exists (lower_bound : nat),
      forall v1 (j : nat) (Hij : (i <= j)%nat)
        limit origin_addr amount msg acts
        prev_cstate inc_calls
        (deployed_prev :
          env_contracts (CStr_nth j str) caddr = Some (contract : WeakContract))
        (deployed_cstate_prev :
          contract_state (CStr_nth j str) caddr = Some prev_cstate)
        (Hinc_calls :
          incoming_calls Msg (CStr_clist str j) caddr = Some inc_calls)
        (queue_prev :
          (CStr_nth j str).(chain_state_queue) =
            build_act limit origin_addr origin_addr
              (match msg with
               | Some m => act_call caddr amount (serialize m)
               | None => act_transfer caddr amount
               end) :: acts)
        (enough_limit : (lower_bound <= limit)%nat)
        (spec_origin_addr : origin_addr_spec s origin_addr)
        (spec_amount : amount_spec s amount)
        (spec_msg : msg_spec s msg)
        (prev_rank :
          rank_fun (chain_height (CStr_nth j str)) (current_slot (CStr_nth j str))
            (finalized_height (CStr_nth j str)) caddr initial_dep_info prev_cstate
            (env_account_balances (CStr_nth j str) caddr) (outgoing_acts (CStr_nth j str) caddr)
            inc_calls (outgoing_txs (CStr_clist str j) caddr) = Some v1)
        (not_bottom : v1 <> bot)
        (tag : TagCallDecrease),
        exists finish
          (action_trace : ActionChainTrace (CStr_nth j str) finish),
          finish.(chain_state_queue) = acts /\
          forall (finish_cstate : State) finish_inc_calls,
            contract_state finish caddr = Some finish_cstate ->
            incoming_calls_action_trace Msg action_trace caddr = Some finish_inc_calls ->
            rank_lt R
              (rank_fun (chain_height (CStr_nth j str)) (current_slot (CStr_nth j str))
                 (finalized_height (CStr_nth j str)) caddr initial_dep_info finish_cstate
                 (env_account_balances finish caddr)
                 []
                 (finish_inc_calls ++ inc_calls)
                 (outgoing_txs_action_trace action_trace caddr ++ outgoing_txs (CStr_clist str j) caddr))
              v1
    ) ->
    forall v1,
      let Rank_Some := fun ch cs fh a dep cst bal out inc txs =>
        rank_fun ch cs fh a dep cst bal out inc txs = Some v1 /\ v1 <> bot in
      let Decrease := fun ch cs fh a dep cst bal out inc txs =>
        exists v2, rank_fun ch cs fh a dep cst bal out inc txs = Some v2 /\ R v2 v1 in
      satisfies contract caddr str i
        (ltl_G (ltl_impl (ltl_and ltl_dep (ltl_atom Rank_Some))
                         (ltl_U ltl_true (ltl_atom Decrease)))).
  Proof.
    intros Hcio deployed_i Hdep_i Hrank_i add_block_case outgoing_act_case
      nonrecursive_call_case recursive_call_case call_spec_decrease v1 Rank_Some Decrease.
    cbn [satisfies]. intros j Hij [Hdep_j Hatom_j].
    apply satisfies_ltl_dep_iff in Hdep_j. rename Hdep_j into deployed_j.
    cbn [satisfies] in Hatom_j.
    destruct (Hatom_j deployed_j) as (d_j & c_j & l_j & Hd_j & Hc_j & Hl_j & Hr_j & Hnb).

    assert (step : forall n v, (j <= n)%nat -> RankAt rank_fun caddr str n v -> v <> bot ->
      exists v', RankAt rank_fun caddr str (S n) v' /\
        le_R R v' v).
    { intros n v Hjn (d & c & l & Hd & Hc & Hl & Hr) Hnb_v.
      pose proof (CStr_wc_preserve str deployed_j n Hjn) as deployed_n.
      destruct (rank_step R bot rank_fun contract caddr (rank_le R)
                  add_block_case
                  outgoing_act_case nonrecursive_call_case recursive_call_case
                  (CStr_nth n str) (CStr_nth (S n) str) (CStr_clist str n)
                  (CStr_nth_reachable str start n) (CStr_link str n) v d c l
                  deployed_n Hd Hc Hl Hr Hnb_v)
        as (d' & c' & l' & Hd' & Hc' & Hl' & Hcase).
      rewrite <- CStr_clist_snoc in Hd', Hl', Hcase.
      cbv zeta in Hcase.
      match type of Hcase with
      | context [rank_fun ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
          destruct (rank_fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [v'|] eqn:Hr'
      end.
      - exists v'. split.
        + exists d', c', l'. repeat split; assumption.
        + destruct Hcase as [(_ & Hle) | (_ & Hle)]; exact Hle.
      - destruct Hcase as [(_ & []) | (_ & [])]. }

    assert (dec_intro : forall k v2, RankAt rank_fun caddr str k v2 -> R v2 v1 ->
      satisfies contract caddr str k (ltl_atom Decrease)).
    { intros k v2 (d & c & l & Hd & Hc & Hl & Hr) HR.
      cbn [satisfies]. intros _. exists d, c, l. repeat split; try assumption.
      exists v2. split; assumption. }
    assert (rank_le_or_dec : forall a, (j <= a)%nat ->
      (exists v, RankAt rank_fun caddr str a v /\ le_R R v v1) \/
      (exists k, (j <= k)%nat /\ satisfies contract caddr str k (ltl_atom Decrease))).
    { intros a Hja.
      remember (a - j)%nat as dd eqn:Hdd. generalize dependent a.
      induction dd as [|dd IH]; intros a Hdd Hja.
      - assert (a = j) by lia. subst a. left. exists v1. split.
        + exists d_j, c_j, l_j. repeat split; assumption.
        + right. reflexivity.
      - destruct a as [|a']; [lia|].
        destruct (IH a' ltac:(lia) ltac:(lia)) as [(v & Hra & Hle) | Hdec]; [|right; exact Hdec].
        destruct (eq_decA v bot) as [-> | Hnb_v].
        + right. exists a'. split; [lia|]. apply (dec_intro a' bot Hra).
          destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq].
        + destruct (step a' v ltac:(lia) Hra Hnb_v) as (v' & Hra' & Hcase).
          left. exists v'. split; [exact Hra'|].
          eapply le_R_trans; eauto. }

    destruct call_spec_decrease as (lower_bound & Hcall_decrease).
    destruct (Hcio lower_bound j) as (m & Hq).
    destruct Hq as (limit & origin_addr & amount & msg & Hlim & Hso & Hsa & Hsm & Hin).
    set (spec_act :=
      build_act limit origin_addr origin_addr
        (match msg with
         | Some m => act_call caddr amount (serialize m)
         | None => act_transfer caddr amount
         end)) in *.
    destruct (cstr_act_hd_finally str start (j + m) spec_act Hin) as (h & Hjmh & Hhd_h).
    destruct (chain_state_queue (CStr_nth h str)) as [|hd acts] eqn:queue_h; [discriminate|].
    cbn in Hhd_h. inversion Hhd_h; subst hd; clear Hhd_h.
    pose proof (CStr_nth_reachable str start h) as reach_h.
    pose proof (CStr_wc_preserve str deployed_j h ltac:(lia)) as deployed_h.
    assert (Hfrom_account : act_is_from_account spec_act).
    { pose proof (origin_is_always_account reach_h) as Horigins.
      rewrite queue_h in Horigins.
      inversion Horigins as [|? ? Horigin_account _]; subst.
      unfold act_origin_is_account in Horigin_account.
      unfold act_is_from_account. cbn in *. exact Horigin_account. }
    assert (Hfinal : exists k, (j <= k)%nat /\ satisfies contract caddr str k (ltl_atom Decrease)).
    { destruct (rank_le_or_dec h ltac:(lia)) as [(v & Hra & Hle) | Hdec]; [|exact Hdec].
      destruct (eq_decA v bot) as [-> | Hnb_v].
      { exists h. split; [lia|]. apply (dec_intro h bot Hra).
        destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq]. }
      destruct Hra as (d_h & c_h & l_h & Hd_h & Hc_h & Hl_h & Hr_h).
      assert (d_h = initial_dep_info).
      { pose proof (CStr_dep_info_preserve str Hdep_i h ltac:(lia)) as Hpres. congruence. }
      subst d_h.
      destruct (Hcall_decrease v h ltac:(lia) limit origin_addr amount msg acts c_h l_h
                  deployed_h Hc_h Hl_h queue_h Hlim Hso Hsa Hsm Hr_h Hnb_v tag_call_decrease)
        as (finish & action_trace & Hfinish_queue & Hdecr).
      destruct (action_trace_cstr_nth_correspond str start h spec_act acts finish action_trace
                  caddr l_h reach_h queue_h Hfrom_account Hfinish_queue Hl_h)
        as (k & Hhk & Henv_fk & Hq_fk & Hchain_hk & Hinc_k & Htxs_k).
      destruct (rank_le_or_dec k ltac:(lia)) as [(v_k & Hra_k & _) | Hdec]; [|exact Hdec].
      exists k. split; [lia|]. apply (dec_intro k v_k Hra_k).
      destruct Hra_k as (d_k & c_k & l_k & Hd_k & Hc_k & Hl_k & Hr_k).
      assert (d_k = initial_dep_info).
      { pose proof (CStr_dep_info_preserve str Hdep_i k ltac:(lia)) as Hpres. congruence. }
      subst d_k.
      destruct (incoming_calls_action_trace Msg action_trace caddr) as [fin_inc|] eqn:Hfin_inc;
        rewrite Hl_k in Hinc_k; [|discriminate].
      injection Hinc_k as ->.
      assert (Hc_f : contract_state finish caddr = Some c_k) by (rewrite Henv_fk; exact Hc_k).
      pose proof (Hdecr c_k fin_inc Hc_f eq_refl) as Hlt.

      assert (Hacts_account : Forall act_is_from_account acts).
      { eapply reachable_queue_tail_accounts_from_account; eauto. }
      assert (Hout_k : outgoing_acts (CStr_nth k str) caddr = []).
      { apply outgoing_acts_after_block_nil.
        - rewrite <- Hq_fk, Hfinish_queue. exact Hacts_account.
        - eapply contract_addr_format; eauto. }
      rewrite Hout_k, Htxs_k in Hr_k.
      assert (Hbal : env_account_balances finish caddr = env_account_balances (CStr_nth k str) caddr)
        by (rewrite Henv_fk; reflexivity).
      rewrite Hbal in Hlt.
      assert (Hch : chain_height (CStr_nth h str) = chain_height (CStr_nth k str) /\
                    current_slot (CStr_nth h str) = current_slot (CStr_nth k str) /\
                    finalized_height (CStr_nth h str) = finalized_height (CStr_nth k str)).
      { rewrite Hchain_hk. repeat split; reflexivity. }
      destruct Hch as (Hch1 & Hch2 & Hch3).
      rewrite Hch1, Hch2, Hch3, Hr_k in Hlt.
      cbn in Hlt.
      destruct Hle as [HR | <-]; [eapply transR; eauto | exact Hlt]. }
    destruct Hfinal as (k & Hjk & Hdec).
    exists k. split; [lia|]. split; [intros; exact I|]. exact Hdec.
  Qed.

  (* Print Assumptions solve_U_eventually_decrease_spec. *)

End SolveU.

Section SolveUEn.
  Context {BaseTypes : ChainBase}.
  Context {Setup Msg State Error : Type}.
  Context `{ser_setup : Serializable Setup}
          `{ser_msg   : Serializable Msg}
          `{ser_state : Serializable State}
          `{ser_error : Serializable Error}.

  Local Notation formula := (@MyLTLBase.formula BaseTypes Setup Msg State).

  Definition call_info_spec (s : @CallSpec BaseTypes Msg) (c : ContractCallInfo Msg) : Prop :=
    call_from c = call_origin c /\ origin_addr_spec s (call_origin c) /\
    amount_spec s (call_amount c) /\ msg_spec s (call_msg c).

  Definition inc_atom (P : list (ContractCallInfo Msg) -> Prop) : formula :=
    ltl_atom (fun _ _ _ _ _ _ _ _ inc _ => P inc).

  Definition IncEven : formula := inc_atom (fun inc => Nat.even (List.length inc) = true).
  Definition HeadSpec (s : CallSpec) : formula :=
    inc_atom (fun inc => exists c tl, inc = c :: tl /\ call_info_spec s c).

  Definition Taken (s : CallSpec) : formula :=
    ltl_or (ltl_and IncEven (ltl_X (ltl_and (ltl_not IncEven) (HeadSpec s))))
           (ltl_and (ltl_not IncEven) (ltl_X (ltl_and IncEven (HeadSpec s)))).

  Lemma incoming_calls_step {from mid to : ChainState}
        (trace : ChainTrace from mid) (step : ChainStep mid to) caddr inc inc' :
    incoming_calls Msg trace caddr = Some inc ->
    incoming_calls Msg (snoc trace step) caddr = Some inc' ->
    inc' = inc \/ exists c, inc' = c :: inc.
  Proof.
    intros Hinc Hinc'.
    destruct_chain_step.
    - cbn in Hinc'. left. congruence.
    - destruct_action_eval; cbn in Hinc'; try (left; congruence).
      destruct (to_addr =? caddr)%address; cbn in Hinc'; [|left; congruence].
      destruct msg as [m|]; [destruct (deserialize m) |]; cbn in Hinc'; try discriminate;
        rewrite Hinc in Hinc'; cbn in Hinc'; injection Hinc' as <-; right; eexists; reflexivity.
    - destruct_action_eval; cbn in Hinc'; try (left; congruence).
      destruct (to_addr =? caddr)%address; cbn in Hinc'; [|left; congruence].
      destruct msg as [m|]; [destruct (deserialize m) |]; cbn in Hinc'; try discriminate;
        rewrite Hinc in Hinc'; cbn in Hinc'; injection Hinc' as <-; right; eexists; reflexivity.
    - cbn in Hinc'. left. congruence.
  Qed.

  Lemma cons_neq {T} (x : T) l : l <> x :: l.
  Proof. intros H. apply (f_equal (@List.length T)) in H. cbn in H. lia. Qed.

  Section RankStepSpec.
  Context {A : Type} (R : A -> A -> Prop) (bot : A).
  Variable rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                      Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A.
  Variable contract : Contract Setup Msg State Error.
  Variable caddr : Address.
  Variable s : @CallSpec BaseTypes Msg.
  Variable en : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> Prop.

  Lemma rank_step_spec
      (spec_call_case :
        forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_user : ctx_from ctx = ctx_origin ctx)
               (spec_origin : origin_addr_spec s (ctx_origin ctx))
               (spec_amount : amount_spec s (ctx_amount ctx))
               (spec_msg : msg_spec s msg)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_en : en (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs)
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagCallDecrease),
          rank_lt R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1)
      {from : ChainState} (mid to : ChainState) (trace : ChainTrace from mid) (reach : reachable mid)
      (step : ChainStep mid to)
      (v1 : A) dep cst inc c :
    env_contracts mid caddr = Some (contract : WeakContract) ->
    deployment_info Setup trace caddr = Some dep ->
    contract_state mid caddr = Some cst ->
    incoming_calls Msg trace caddr = Some inc ->
    rank_fun (chain_height mid) (current_slot mid) (finalized_height mid) caddr dep cst
      (env_account_balances mid caddr) (outgoing_acts mid caddr) inc (outgoing_txs trace caddr) = Some v1 ->
    v1 <> bot ->
    en (chain_height mid) (current_slot mid) (finalized_height mid) caddr dep cst
      (env_account_balances mid caddr) (outgoing_acts mid caddr) inc (outgoing_txs trace caddr) ->
    incoming_calls Msg (snoc trace step) caddr = Some (c :: inc) ->
    call_info_spec s c ->
    exists cst',
      deployment_info Setup (snoc trace step) caddr = Some dep /\
      contract_state to caddr = Some cst' /\
      rank_lt R (rank_fun (chain_height to) (current_slot to) (finalized_height to) caddr dep cst'
                   (env_account_balances to caddr) (outgoing_acts to caddr) (c :: inc)
                   (outgoing_txs (snoc trace step) caddr)) v1.
  Proof.
    intros deployed Hdep Hcst Hinc Hrank not_bot Hen Hinc' Hspec.
    assert (is_contract : address_is_contract caddr = true)
      by (eapply contract_addr_format; eauto).
    pose proof (origin_is_always_account reach) as Horigins.
    remember (outgoing_acts to caddr) as out_to eqn:Hout_to.
    destruct_chain_step.
    -
      exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
    - (* user action *)
      destruct_action_eval.
      + exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
      + exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
      + destruct (address_eqb_spec to_addr caddr) as [->|Hto].
        2: { exfalso. cbn in Hinc'. rewrite (address_eq_ne to_addr caddr Hto) in Hinc'.
             apply (cons_neq c inc). congruence. }

        assert (Hfrom : from_addr <> caddr).
        { intros ->. unfold act_is_from_account in from_acc. subst act. cbn in from_acc. congruence. }
        unfold outgoing_acts in *. rewrite queue_prev in Hrank, Hen. rewrite queue_new in Hout_to. subst out_to act new_acts.
        assert (Hwc : wc = (contract : WeakContract)) by congruence. subst wc.
        destruct (wc_receive_strong receive_some)
          as (prev_state_strong & msg_strong & resp_state_strong &
              deser_state & deser_msg & <- & receive).

        assert (Hc : c = build_call_info limit origin from_addr amount msg_strong).
        { cbn in Hinc'. rewrite address_eq_refl in Hinc'.
          destruct msg_strong as [ms|], msg as [m|]; cbn in deser_msg; try congruence;
            [rewrite deser_msg in Hinc' | ]; cbn in Hinc'; rewrite Hinc in Hinc'; cbn in Hinc'; congruence. }
        subst c.
        destruct Hspec as (Hfrom_origin & Hspec_origin & Hspec_amount & Hspec_msg).
        cbn in Hfrom_origin, Hspec_origin, Hspec_amount, Hspec_msg.
        unfold contract_state in Hcst. rewrite deployed_state in Hcst. cbn in Hcst.
        replace prev_state_strong with cst in * by congruence.
        cbn in Hrank, Hen |- *.
        rewrite filter_app, filter_map, map_app, map_map in *; cbn in *.
        assert (Hbal_to : env_account_balances to caddr = (amount + env_account_balances mid caddr)%Z).
        { rewrite env_eq; cbn. rewrite address_eq_refl.
          rewrite (address_eq_ne caddr from_addr) by auto. cbn. lia. }
        exists resp_state_strong.
        rewrite env_eq; cbn.
        rewrite address_eq_refl; cbn.
        rewrite deserialize_serialize.
        split; [assumption|]. split; [reflexivity|].
        rewrite filter_true, map_id.
        fold (outgoing_txs trace caddr) in *.
        rewrite ?(address_eq_ne caddr from_addr), ?(address_eq_ne from_addr caddr) in * by auto.
        cbn in *.
        replace (amount + env_account_balances mid caddr)%Z with (env_account_balances to caddr) by lia.
        replace (env_account_balances mid caddr)
          with (env_account_balances to caddr - amount)%Z in Hrank, Hen by lia.
        eapply (spec_call_case v1 (transfer_balance from_addr caddr amount mid) dep cst
                  _ inc _
                  (build_ctx limit origin from_addr caddr (env_account_balances to caddr) amount) msg_strong);
          cbn; eauto; try constructor.
    -
      destruct_action_eval.
      + exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
      + exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
      + exfalso.
        destruct (address_eqb_spec to_addr caddr) as [->|Hto].
        2: { cbn in Hinc'. rewrite (address_eq_ne to_addr caddr Hto) in Hinc'.
             apply (cons_neq c inc). congruence. }
        assert (Hwc : wc = (contract : WeakContract)) by congruence. subst wc.
        destruct (wc_receive_strong receive_some)
          as (prev_state_strong & msg_strong & resp_state_strong &
              deser_state & deser_msg & <- & receive).
        assert (Hc : c = build_call_info limit origin from_addr amount msg_strong).
        { cbn in Hinc'. rewrite address_eq_refl in Hinc'.
          destruct msg_strong as [ms|], msg as [m|]; cbn in deser_msg; try congruence;
            [rewrite deser_msg in Hinc' | ]; cbn in Hinc'; rewrite Hinc in Hinc'; cbn in Hinc'; congruence. }
        subst c.
        destruct Hspec as (Hfrom_origin & _). cbn in Hfrom_origin. subst from_addr.
        rewrite queue_prev in Horigins. inversion Horigins as [|? ? Horigin _]; subst.
        unfold act_origin_is_account in Horigin. unfold act_is_from_contract in from_contract.
        cbn in Horigin, from_contract. congruence.
    - exfalso. cbn in Hinc'. apply (cons_neq c inc). congruence.
  Qed.
  End RankStepSpec.

  Definition Enabled (contract : Contract Setup Msg State Error) (s : CallSpec)
      (ch cs fh : nat) (addr : Address) (_ : DeploymentInfo Setup) (cst : State) (bal : Amount)
      (_ : list ActionBody) (_ : list (ContractCallInfo Msg)) (_ : list Tx) : Prop :=
    exists limit origin_addr amount msg new_cst acts,
      (0 < limit)%nat /\ address_is_contract origin_addr = false /\
      origin_addr_spec s origin_addr /\ amount_spec s amount /\ (0 <= amount)%Z /\ msg_spec s msg /\
      receive contract (build_chain ch cs fh)
              (build_ctx limit origin_addr origin_addr addr (bal + amount) amount) cst msg
      = Ok (new_cst, acts).

  Definition EnabledNoActs (contract : Contract Setup Msg State Error) (s : CallSpec)
      (ch cs fh : nat) (addr : Address) (_ : DeploymentInfo Setup) (cst : State) (bal : Amount)
      (_ : list ActionBody) (_ : list (ContractCallInfo Msg)) (_ : list Tx) : Prop :=
    exists limit origin_addr amount msg new_cst,
      (0 < limit)%nat /\ address_is_contract origin_addr = false /\
      origin_addr_spec s origin_addr /\ amount_spec s amount /\ (0 <= amount)%Z /\ msg_spec s msg /\
      receive contract (build_chain ch cs fh)
              (build_ctx limit origin_addr origin_addr addr (bal + amount) amount) cst msg
      = Ok (new_cst, []).

  Record EnabledCond (contract : Contract Setup Msg State Error) (s : CallSpec) := {
    en : @Atom BaseTypes Setup Msg State;
    en_sound : forall ch cs fh addr dep cst bal out inc txs,
      en ch cs fh addr dep cst bal out inc txs -> Enabled contract s ch cs fh addr dep cst bal out inc txs
  }.
  Global Arguments en {_ _}.
  Global Arguments en_sound {_ _}.

  Definition default_en contract s : EnabledCond contract s :=
    {| en := Enabled contract s;
       en_sound := fun ch cs fh addr dep cst bal out inc txs H => H |}.

  Definition no_acts_en contract s : EnabledCond contract s.
  Proof.
    refine {| en := EnabledNoActs contract s |}.
    intros ch cs fh addr dep cst bal out inc txs
      (limit & origin_addr & amount & msg & new_cst & H).
    exists limit, origin_addr, amount, msg, new_cst, []. exact H.
  Defined.

  Definition called_infinitely_often_until_En contract s (E : EnabledCond contract s) : formula :=
    ltl_G (ltl_impl (ltl_atom (en E))
                    (ltl_U ltl_true (ltl_or (ltl_not (ltl_atom (en E))) (Taken s)))).

  Lemma taken_elim (contract : Contract Setup Msg State Error) (caddr : Address) (str : ChainStream)
      (s : CallSpec) (m : nat) (dep : DeploymentInfo Setup) (cst : State) (inc : list (ContractCallInfo Msg)) :
    env_contracts (CStr_nth m str) caddr = Some (contract : WeakContract) ->
    deployment_info Setup (CStr_clist str m) caddr = Some dep ->
    contract_state (CStr_nth m str) caddr = Some cst ->
    incoming_calls Msg (CStr_clist str m) caddr = Some inc ->
    satisfies contract caddr str m (Taken s) ->
    exists c, incoming_calls Msg (CStr_clist str (S m)) caddr = Some (c :: inc) /\ call_info_spec s c.
  Proof.
    intros deployed Hd Hc Hl Htaken.
    pose proof (CStr_wc_preserve str deployed (S m) ltac:(lia)) as deployed_S.
    unfold Taken in Htaken.
    destruct Htaken as [[Hev [Hnev_S Hhead_S]] | [Hnev [Hev_S Hhead_S]]];
      unfold HeadSpec, inc_atom in Hhead_S; cbn [satisfies] in Hhead_S;
      destruct (Hhead_S deployed_S) as (d' & c' & l' & Hd' & Hc' & Hl' & c & tl & Hl'_eq & Hspec);
      pose proof Hl' as Hl'_snoc; rewrite CStr_clist_snoc in Hl'_snoc;
      destruct (incoming_calls_step _ _ caddr inc l' Hl Hl'_snoc) as [Heq | (c0 & Heq)].
    -
      exfalso. apply Hnev_S.
      unfold IncEven, inc_atom in *. cbn [satisfies] in *. intros _.
      exists d', c', l'. repeat split; try assumption.
      subst l'. destruct (Hev deployed) as (d0 & c0 & l0 & _ & _ & Hl0 & Heven). congruence.
    - exists c. split; [congruence|exact Hspec].
    -
      exfalso. apply Hnev.
      unfold IncEven, inc_atom in *. cbn [satisfies] in *. intros _.
      exists dep, cst, inc. repeat split; try assumption.
      subst l'. destruct (Hev_S deployed_S) as (d0 & c0 & l0 & _ & _ & Hl0 & Heven). congruence.
    - exists c. split; [congruence|exact Hspec].
  Qed.

  Lemma solve_U_eventually_decrease_en
        (contract : Contract Setup Msg State Error)
        {A : Type}
        (R : A -> A -> Prop)
        (wfR : well_founded R)
        (transR : transitive A R)
        (bot : A)
        (eq_decA : forall x y : A, {x = y} + {x <> y})
        (rank_fun : nat -> nat -> nat -> Address -> DeploymentInfo Setup -> State ->
                    Amount -> list ActionBody -> list (ContractCallInfo Msg) -> list Tx -> option A)
        (caddr : Address)
        (str : ChainStream)
        (start : CStr_nth 0 str = empty_state)
        (i : nat)
        (s : CallSpec)
        (E : EnabledCond contract s) :

    satisfies contract caddr str i (called_infinitely_often_until_En contract s E) ->

    (forall v,
      satisfies contract caddr str i
        (ltl_G (ltl_impl
                  (ltl_and ltl_dep
                     (ltl_atom (fun ch cs fh a dep cst bal out inc txs =>
                                  rank_fun ch cs fh a dep cst bal out inc txs = Some v /\ v <> bot)))
                  (ltl_atom (en E))))) ->
    (* add_block_case *)
    (forall v1 h s f h' s' f' dep cst bal inc txs
               (valid_height : h' = S h) (valid_slot : s < s') (valid_finalized : f <= f' /\ f' < h')
               (prev_rank : rank_fun h s f caddr dep cst bal [] inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagAddBlockDoNotIncrease),
          rank_le R (rank_fun h' s' f' caddr dep cst bal [] inc txs) v1) ->
    (* outgoing_act_case *)
    (forall v1 h s f dep cst bal out_act out_acts inc txs tx
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
               (prev_rank : rank_fun h s f caddr dep cst bal (out_act :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagOutgoingActDoNotIncrease),
          rank_le R (rank_fun h s f caddr dep cst (bal - act_body_amount out_act)%Z out_acts inc (tx :: txs)) v1) ->
    (* nonrecursive_call_case *)
    (forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_other : ctx_from ctx <> caddr)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagNonrecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1) ->
    (* recursive_call_case *)
    (forall v1 chain dep cst head out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_self : ctx_from ctx = caddr)
               (action_facts :
                 match head with
                 | act_transfer to amount => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\ msg = None
                 | act_call to amount msg_ser => to = ctx_contract_address ctx /\ amount = ctx_amount ctx /\
                                                 msg <> None /\ deserialize msg_ser = msg
                 | _ => False
                 end)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx) (head :: out_acts) inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagRecursiveCallDoNotIncrease),
          rank_le R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     (build_tx (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_contract_address ctx) (ctx_amount ctx)
                        (tx_call (match head with act_call _ _ m => Some m | _ => None end)) :: txs)) v1) ->

    (forall v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
               (ctx_addr : ctx_contract_address ctx = caddr)
               (from_user : ctx_from ctx = ctx_origin ctx)
               (spec_origin : origin_addr_spec s (ctx_origin ctx))
               (spec_amount : amount_spec s (ctx_amount ctx))
               (spec_msg : msg_spec s msg)
               (receive_some : receive contract chain ctx cst msg = Ok (new_cst, new_acts))
               (prev_en : en E (chain_height chain) (current_slot chain) (finalized_height chain)
                            caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs)
               (prev_rank : rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                              caddr dep cst (ctx_contract_balance ctx - ctx_amount ctx)%Z out_acts inc txs = Some v1)
               (not_bot : v1 <> bot)
               (tag : TagCallDecrease),
          rank_lt R (rank_fun (chain_height chain) (current_slot chain) (finalized_height chain)
                     caddr dep new_cst (ctx_contract_balance ctx) (new_acts ++ out_acts)
                     (build_call_info (ctx_limit ctx) (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) msg :: inc)
                     txs) v1) ->
    forall v1,
      let Rank_Some := fun ch cs fh a dep cst bal out inc txs =>
        rank_fun ch cs fh a dep cst bal out inc txs = Some v1 /\ v1 <> bot in
      let Decrease := fun ch cs fh a dep cst bal out inc txs =>
        exists v2, rank_fun ch cs fh a dep cst bal out inc txs = Some v2 /\ R v2 v1 in
      satisfies contract caddr str i
        (ltl_G (ltl_impl (ltl_and ltl_dep (ltl_atom Rank_Some))
                         (ltl_U ltl_true (ltl_atom Decrease)))).
  Proof.
    intros Hfair HE2 add_block_case outgoing_act_case
      nonrecursive_call_case recursive_call_case spec_call_case v1 Rank_Some Decrease.
    cbn [satisfies]. intros j Hij [Hdep_j Hatom_j].
    apply satisfies_ltl_dep_iff in Hdep_j. rename Hdep_j into deployed_j.
    cbn [satisfies] in Hatom_j.
    destruct (Hatom_j deployed_j) as (d_j & c_j & l_j & Hd_j & Hc_j & Hl_j & Hr_j & Hnb).

    assert (step : forall n v, (j <= n)%nat -> RankAt rank_fun caddr str n v -> v <> bot ->
      exists v', RankAt rank_fun caddr str (S n) v' /\ le_R R v' v).
    { intros n v Hjn (d & c & l & Hd & Hc & Hl & Hr) Hnb_v.
      pose proof (CStr_wc_preserve str deployed_j n Hjn) as deployed_n.
      destruct (rank_step R bot rank_fun contract caddr (rank_le R)
                  add_block_case
                  outgoing_act_case nonrecursive_call_case recursive_call_case
                  (CStr_nth n str) (CStr_nth (S n) str) (CStr_clist str n)
                  (CStr_nth_reachable str start n) (CStr_link str n) v d c l
                  deployed_n Hd Hc Hl Hr Hnb_v)
        as (d' & c' & l' & Hd' & Hc' & Hl' & Hcase).
      rewrite <- CStr_clist_snoc in Hd', Hl', Hcase.
      cbv zeta in Hcase.
      match type of Hcase with
      | context [rank_fun ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
          destruct (rank_fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [v'|] eqn:Hr'
      end.
      - exists v'. split.
        + exists d', c', l'. repeat split; assumption.
        + destruct Hcase as [(_ & Hle) | (_ & Hle)]; exact Hle.
      - destruct Hcase as [(_ & []) | (_ & [])]. }

    assert (dec_intro : forall k v2, RankAt rank_fun caddr str k v2 -> R v2 v1 ->
      satisfies contract caddr str k (ltl_atom Decrease)).
    { intros k v2 (d & c & l & Hd & Hc & Hl & Hr) HR.
      cbn [satisfies]. intros _. exists d, c, l. repeat split; try assumption.
      exists v2. split; assumption. }
    assert (rank_le_or_dec : forall a, (j <= a)%nat ->
      (exists v, RankAt rank_fun caddr str a v /\ le_R R v v1) \/
      (exists k, (j <= k)%nat /\ satisfies contract caddr str k (ltl_atom Decrease))).
    { intros a Hja.
      remember (a - j)%nat as dd eqn:Hdd. generalize dependent a.
      induction dd as [|dd IH]; intros a Hdd Hja.
      - assert (a = j) by lia. subst a. left. exists v1. split.
        + exists d_j, c_j, l_j. repeat split; assumption.
        + right. reflexivity.
      - destruct a as [|a']; [lia|].
        destruct (IH a' ltac:(lia) ltac:(lia)) as [(v & Hra & Hle) | Hdec]; [|right; exact Hdec].
        destruct (eq_decA v bot) as [-> | Hnb_v].
        + right. exists a'. split; [lia|]. apply (dec_intro a' bot Hra).
          destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq].
        + destruct (step a' v ltac:(lia) Hra Hnb_v) as (v' & Hra' & Hle').
          left. exists v'. split; [exact Hra'|].
          eapply le_R_trans; eauto. }

    assert (en_at : forall n v d c l, (i <= n)%nat ->
      env_contracts (CStr_nth n str) caddr = Some (contract : WeakContract) ->
      deployment_info Setup (CStr_clist str n) caddr = Some d ->
      contract_state (CStr_nth n str) caddr = Some c ->
      incoming_calls Msg (CStr_clist str n) caddr = Some l ->
      rank_fun (chain_height (CStr_nth n str)) (current_slot (CStr_nth n str))
        (finalized_height (CStr_nth n str)) caddr d c
        (env_account_balances (CStr_nth n str) caddr) (outgoing_acts (CStr_nth n str) caddr)
        l (outgoing_txs (CStr_clist str n) caddr) = Some v ->
      v <> bot ->
      en E (chain_height (CStr_nth n str)) (current_slot (CStr_nth n str))
        (finalized_height (CStr_nth n str)) caddr d c
        (env_account_balances (CStr_nth n str) caddr) (outgoing_acts (CStr_nth n str) caddr)
        l (outgoing_txs (CStr_clist str n) caddr)).
    { intros n v d c l Hin deployed_n Hd Hc Hl Hr Hnb_v.
      assert (Hpre : satisfies contract caddr str n
                (ltl_and ltl_dep
                   (ltl_atom (fun ch cs fh a dep cst bal out inc txs =>
                                rank_fun ch cs fh a dep cst bal out inc txs = Some v /\ v <> bot)))).
      { split.
        - apply satisfies_ltl_dep_iff. exact deployed_n.
        - apply (satisfies_atom_intro caddr str start n).
          intros d' c' l' _ Hd' Hc' Hl'.
          replace d' with d by congruence. replace c' with c by congruence. replace l' with l by congruence.
          split; assumption. }
      pose proof (HE2 v n Hin Hpre) as Hen.
      exact (satisfies_atom_elim caddr str n (en E) d c l Hen deployed_n Hd Hc Hl). }

    assert (Hen_j : satisfies contract caddr str j (ltl_atom (en E))).
    { apply (satisfies_atom_intro caddr str start j).
      intros d' c' l' _ Hd' Hc' Hl'.
      replace d' with d_j by congruence. replace c' with c_j by congruence. replace l' with l_j by congruence.
      exact (en_at j v1 d_j c_j l_j Hij deployed_j Hd_j Hc_j Hl_j Hr_j Hnb). }
    destruct (Hfair j Hij Hen_j) as (k & Hjk & _ & Hk).

    assert (Hfinal : exists m, (j <= m)%nat /\ satisfies contract caddr str m (ltl_atom Decrease)).
    { destruct (rank_le_or_dec k Hjk) as [(v & Hra & Hle) | Hdec]; [|exact Hdec].

      destruct (eq_decA v bot) as [-> | Hnb_v].
      { exists k. split; [lia|]. apply (dec_intro k bot Hra).
        destruct Hle as [HR | Heq]; [exact HR | exfalso; apply Hnb; exact Heq]. }
      pose proof (CStr_wc_preserve str deployed_j k Hjk) as deployed_k.
      destruct Hra as (d_k & c_k & l_k & Hd_k & Hc_k & Hl_k & Hr_k).
      pose proof (en_at k v d_k c_k l_k ltac:(lia) deployed_k Hd_k Hc_k Hl_k Hr_k Hnb_v) as Hen_k.
      destruct Hk as [Hnen_k | Htaken_k].
      -
        exfalso. apply Hnen_k.
        apply (satisfies_atom_intro caddr str start k).
        intros d' c' l' _ Hd' Hc' Hl'.
        replace d' with d_k by congruence. replace c' with c_k by congruence. replace l' with l_k by congruence.
        exact Hen_k.
      -
        destruct (taken_elim contract caddr str s k d_k c_k l_k deployed_k Hd_k Hc_k Hl_k Htaken_k)
          as (c & Hl_Sk & Hspec).
        rewrite CStr_clist_snoc in Hl_Sk.
        destruct (rank_step_spec R bot rank_fun contract caddr s (en E) spec_call_case
                    (CStr_nth k str) (CStr_nth (S k) str) (CStr_clist str k)
                    (CStr_nth_reachable str start k) (CStr_link str k) v d_k c_k l_k c
                    deployed_k Hd_k Hc_k Hl_k Hr_k Hnb_v Hen_k Hl_Sk Hspec)
          as (c' & Hd_Sk & Hc_Sk & Hlt).
        rewrite <- CStr_clist_snoc in Hd_Sk, Hl_Sk, Hlt.
        destruct (rank_fun _ _ _ _ _ _ _ _ _ _) as [v'|] eqn:Hr_Sk in Hlt; [|destruct Hlt].
        exists (S k). split; [lia|].
        apply (dec_intro (S k) v').
        + exists d_k, c', (c :: l_k). repeat split; assumption.
        + destruct Hle as [HR | <-]; [eapply transR; eauto | exact Hlt]. }
    destruct Hfinal as (m & Hjm & Hdec).
    exists m. split; [lia|]. split; [intros; exact I|]. exact Hdec.
  Qed.
End SolveUEn.

Ltac solve_rank_unchanged :=
  intros;
  match goal with
  | H : ?r1 = Some ?v |- rank_le _ ?r2 ?v =>
      replace r2 with r1 by reflexivity; rewrite H; apply rank_le_refl
  end.

Tactic Notation "solve_U_block" constr(R) constr(wfR) constr(transR) constr(bot) constr(eq_decA) constr(rank_fun) :=
  match goal with
  | start : CStr_nth 0 ?str = empty_state |- satisfies ?contract ?caddr ?str ?i (ltl_U ?x ?y) =>
      apply (solve_U R wfR bot eq_decA rank_fun contract caddr str start x y i);
      [ | | eapply (solve_U_eventually_decrease contract R wfR transR bot eq_decA rank_fun caddr str start i) | ];
      try solve_rank_unchanged
  end.

Tactic Notation "solve_U_spec" constr(R) constr(wfR) constr(transR) constr(bot) constr(eq_decA) constr(rank_fun) constr(s) :=
  match goal with
  | start : CStr_nth 0 ?str = empty_state |- satisfies ?contract ?caddr ?str ?i (ltl_U ?x ?y) =>
      apply (solve_U R wfR bot eq_decA rank_fun contract caddr str start x y i);
      [ | | eapply (solve_U_eventually_decrease_spec contract R wfR transR bot eq_decA rank_fun caddr str start i _ s) | ];
      try solve_rank_unchanged
  end.

Tactic Notation "solve_U_en" constr(R) constr(wfR) constr(transR) constr(bot) constr(eq_decA) constr(rank_fun) constr(s) constr(E) :=
  match goal with
  | start : CStr_nth 0 ?str = empty_state |- satisfies ?contract ?caddr ?str ?i (ltl_U ?x ?y) =>
      apply (solve_U R wfR bot eq_decA rank_fun contract caddr str start x y i);
      [ | | eapply (solve_U_eventually_decrease_en contract R wfR transR bot eq_decA rank_fun caddr str start i s E) | ];
      try solve_rank_unchanged
  end.

Global Notation "'Please' 'show' 'that' 'the' 'rank' 'does' 'not' 'increase' 'after' 'a' 'call'" :=
  TagCallDoNotIncrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'rank' 'does' 'not' 'increase' 'after' 'addition' 'of' 'a' 'block'" :=
  TagAddBlockDoNotIncrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'rank' 'does' 'not' 'increase' 'after' 'an' 'outgoing' 'action'" :=
  TagOutgoingActDoNotIncrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'rank' 'does' 'not' 'increase' 'after' 'a' 'nonrecursive' 'call'" :=
  TagNonrecursiveCallDoNotIncrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'rank' 'does' 'not' 'increase' 'after' 'a' 'recursive' 'call'" :=
  TagRecursiveCallDoNotIncrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'specified' 'call' 'strictly' 'decreases' 'the' 'rank'" :=
  TagCallDecrease (at level 100, only printing).
Global Notation "'Please' 'show' 'that' 'the' 'rank' 'strictly' 'decreases' 'after' 'addition' 'of' 'a' 'block'" :=
  TagAddBlockDecrease (at level 100, only printing).

