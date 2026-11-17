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

From ConCert.Examples.Wip.LTL Require Import MyLTLBase.

Bind Scope Z_scope with Amount.

Local Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
  end.

Section LTL_G.
  Context {BaseTypes : ChainBase}.

Section PathSemantics_G.
  Context {Setup Msg State Error : Type}.
  Context `{ser_setup : Serializable Setup}
          `{ser_msg   : Serializable Msg}
          `{ser_state : Serializable State}
          `{ser_error : Serializable Error}.

Section Solve_G.

  Definition contract_view_unchanged
      (contract : Contract Setup Msg State Error)
      (caddr : Address)
      (str : ChainStream)
      (i : nat) : Prop :=
    let st := CStr_nth i str in
    let st' := CStr_nth (S i) str in
    let trace := CStr_clist str i in
    let trace' := CStr_clist str (S i) in
    env_contracts st caddr = env_contracts st' caddr /\
    (env_contracts st' caddr = Some (contract : WeakContract) ->
      deployment_info Setup trace caddr = deployment_info Setup trace' caddr /\
      @contract_state BaseTypes State _ st caddr = @contract_state BaseTypes State _ st' caddr /\
      incoming_calls Msg trace caddr = incoming_calls Msg trace' caddr /\
      outgoing_txs trace caddr = outgoing_txs trace' caddr /\
      st.(chain_height) = st'.(chain_height) /\
      st.(current_slot) = st'.(current_slot) /\
      st.(finalized_height) = st'.(finalized_height) /\
      env_account_balances st caddr = env_account_balances st' caddr /\
      outgoing_acts st caddr = outgoing_acts st' caddr).

  Local Ltac use_x_free Hxf :=
    cbn [x_free] in Hxf; try discriminate Hxf;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | IH : forall i : nat, x_free ?g = true -> @?Q i, H : x_free ?g = true |- _ =>
          let IH' := fresh "IH" in
          pose proof (fun i => IH i H) as IH'; clear IH; rename IH' into IH
      end.

  Lemma satis_equiv
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (i : nat) (f : formula) :
    x_free f = true ->
    contract_view_unchanged contract caddr str i ->
    (satisfies contract caddr str i f <-> satisfies contract caddr str (S i) f).
  Proof.
    revert i.
    induction f as
      [P
      | (* true *)
      | (* false *)
      | f IH
      | f1 IH1 f2 IH2
      | f1 IH1 f2 IH2
      | f1 IH1 f2 IH2
      | f IH
      | f1 IH1 f2 IH2
      | f IH];
      intros i Hxf Hview; use_x_free Hxf.

    - (* ltl_atom *)
      unfold contract_view_unchanged in Hview.
      destruct Hview as (Henv_eq & Hview_detail).
      split.
      + intros Hsat Henv_next.
        assert (Henv_now :
          env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract)).
        { rewrite Henv_eq. exact Henv_next. }
        destruct (Hview_detail Henv_next) as
          (Hdep & Hstate & Hinc & Htxs & Hheight & Hslot & Hfinal & Hbalance & Houtacts).
        cbn [satisfies] in Hsat.
        destruct_deployed_typed.
        exists dep_info0, cstate0, inc_calls0.
        repeat split.
        * rewrite <- Hdep. exact Hdep_info.
        * rewrite <- Hstate. exact Hcstate.
        * rewrite <- Hinc. exact Hinc_calls.
        * rewrite <- Hheight, <- Hslot, <- Hfinal, <- Hbalance,
                    <- Houtacts, <- Htxs.
          assumption.
      + intros Hsat Henv_now.
        assert (Henv_next :
          env_contracts (CStr_nth (S i) str) caddr = Some (contract : WeakContract)).
        { rewrite <- Henv_eq. exact Henv_now. }
        destruct (Hview_detail Henv_next) as
          (Hdep & Hstate & Hinc & Htxs & Hheight & Hslot & Hfinal & Hbalance & Houtacts).
        cbn [satisfies] in Hsat.
        destruct_deployed_typed.
        exists dep_info0, cstate0, inc_calls0.
        repeat split.
        * rewrite Hdep. exact Hdep_info.
        * rewrite Hstate. exact Hcstate.
        * rewrite Hinc. exact Hinc_calls.
        * rewrite Hheight, Hslot, Hfinal, Hbalance, Houtacts, Htxs.
          assumption.

    - (* ltl_true *)
      tauto.

    - (* ltl_false *)
      tauto.

    - (* ltl_not *)
      cbn; specialize (IH i Hview); tauto.

    - (* ltl_and *)
      cbn; specialize (IH1 i Hview); specialize (IH2 i Hview); tauto.

    - (* ltl_or *)
      cbn; specialize (IH1 i Hview); specialize (IH2 i Hview); tauto.

    - (* ltl_impl *)
      cbn; specialize (IH1 i Hview); specialize (IH2 i Hview); tauto.

    - (* ltl_G *)
      split; intros Hsat j Hj.
      + apply Hsat. lia.
      + assert (Hcases : j = i \/ (S i <= j)%nat) by lia.
        destruct Hcases as [Heq | Hgt].
        * subst j. apply IH; auto.
        * apply Hsat. lia.

    - (* ltl_U *)
      cbn; split; intros (j & Hj_ge & Hk_x & Hj_y).
      + assert (Hcases : i = j \/ (i < j)%nat) by lia.
        destruct Hcases as [Heq | Hlt].
        * subst j. exists (S i). repeat split.
          -- lia.
          -- intros k Hk1 Hk2. lia.
          -- apply IH2 with (i := i); auto.
        * exists j. repeat split.
          -- lia.
          -- intros k Hk1 Hk2. apply Hk_x; lia.
          -- exact Hj_y.
      + assert (Hcases : j = S i \/ (S i < j)%nat) by lia.
        destruct Hcases as [Heq | Hlt].
        * subst j. exists i. repeat split.
          -- lia.
          -- intros k Hk1 Hk2. lia.
          -- apply IH2; auto.
        * exists j. repeat split.
          -- lia.
          -- intros k Hk1 Hk2.
             assert (Hk_cases : k = i \/ (S i <= k)%nat) by lia.
             destruct Hk_cases as [Hk_eq | Hk_ge].
             ++ subst k. apply IH1; auto.
             ++ apply Hk_x; lia.
          -- exact Hj_y.
  Qed.

  Lemma satis_equiv_forward
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (i : nat) (f : formula) :
    x_free f = true ->
    contract_view_unchanged contract caddr str i ->
    satisfies contract caddr str i f ->
    satisfies contract caddr str (S i) f.
  Proof.
    intros Hxf Hview Hsat.
    destruct (satis_equiv contract caddr str i f Hxf Hview)
      as [Hforward _].
    exact (Hforward Hsat).
  Qed.

  Lemma satis_not_deployed_equiv
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (i : nat) (f : formula) :
    x_free f = true ->
    env_contracts (CStr_nth i str) caddr <> Some (contract : WeakContract) ->
    env_contracts (CStr_nth (S i) str) caddr <> Some (contract : WeakContract) ->
    (satisfies contract caddr str i f <-> satisfies contract caddr str (S i) f).
  Proof.
    revert i.
    induction f as
      [P
      | (* true *)
      | (* false *)
      | f IH
      | f1 IH1 f2 IH2
      | f1 IH1 f2 IH2
      | f1 IH1 f2 IH2
      | f IH
      | f1 IH1 f2 IH2
      | f IH];
      intros i Hxf Hnot_now Hnot_next; use_x_free Hxf; cbn [satisfies].

    - split; intros Hsat Hdeployed; congruence.
    - tauto.
    - tauto.
    - specialize (IH i Hnot_now Hnot_next). tauto.
    - specialize (IH1 i Hnot_now Hnot_next).
      specialize (IH2 i Hnot_now Hnot_next). tauto.
    - specialize (IH1 i Hnot_now Hnot_next).
      specialize (IH2 i Hnot_now Hnot_next). tauto.
    - specialize (IH1 i Hnot_now Hnot_next).
      specialize (IH2 i Hnot_now Hnot_next). tauto.
    - split; intros Hsat j Hj.
      + apply Hsat. lia.
      + assert (Hcases : j = i \/ (S i <= j)%nat) by lia.
        destruct Hcases as [Heq | Hge].
        * subst j. apply IH; auto.
        * apply Hsat. lia.
    - split; intros (j & Hj_ge & Hk_x & Hj_y).
      + assert (Hcases : i = j \/ (i < j)%nat) by lia.
        destruct Hcases as [Heq | Hlt].
        * subst j. exists (S i). repeat split; try lia.
          apply IH2 with (i := i); auto.
        * exists j. repeat split; try lia.
          -- intros k Hk1 Hk2. apply Hk_x; lia.
          -- exact Hj_y.
      + assert (Hcases : j = S i \/ (S i < j)%nat) by lia.
        destruct Hcases as [Heq | Hlt].
        * subst j. exists i. repeat split; try lia.
          apply IH2; auto.
        * exists j. repeat split; try lia.
          -- intros k Hk1 Hk2.
             assert (Hk_cases : k = i \/ (S i <= k)%nat) by lia.
             destruct Hk_cases as [Hk_eq | Hk_ge].
             ++ subst k. apply IH1; auto.
             ++ apply Hk_x; lia.
          -- exact Hj_y.
  Qed.

  Lemma satis_not_deployed_forward
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (i : nat) (f : formula) :
    x_free f = true ->
    env_contracts (CStr_nth i str) caddr <> Some (contract : WeakContract) ->
    env_contracts (CStr_nth (S i) str) caddr <> Some (contract : WeakContract) ->
    satisfies contract caddr str i f ->
    satisfies contract caddr str (S i) f.
  Proof.
    intros Hxf Hnot_now Hnot_next Hsat.
    destruct
      (satis_not_deployed_equiv contract caddr str i f Hxf Hnot_now Hnot_next)
      as [Hforward _].
    exact (Hforward Hsat).
  Qed.

  Local Ltac expose_next_trace :=
    match goal with
    | Htrace :
        CStr_clist ?str (S ?i) =
        snoc (CStr_clist ?str ?i) ?step
      |- context[CStr_clist ?str (S ?i)] =>
        rewrite Htrace; cbn
    | Htrace :
        CStr_clist ?str (S ?i) =
        snoc (CStr_clist ?str ?i) ?step,
      H : context[CStr_clist ?str (S ?i)] |- _ =>
        rewrite Htrace in H; cbn in H
    end.

  Lemma CStr_start_inc_calls_eq
      (bstate : ChainState) (caddr : Address)
      (str : ChainStream)
      (start : CStr_nth 0 str = bstate) i :
    incoming_calls Msg (CStr_clist_start str start i) caddr
      = incoming_calls Msg (CStr_clist str i) caddr.
  Proof.
    intros. destruct start. auto.
  Qed.

  Lemma CStr_start_out_txs_eq
      (bstate : ChainState) (caddr : Address)
      (str : ChainStream)
      (start : CStr_nth 0 str = bstate) i :
    outgoing_txs (CStr_clist_start str start i) caddr
      = outgoing_txs (CStr_clist str i) caddr.
  Proof.
    intros. destruct start. auto.
  Qed.

  Hint Constructors
    TagFacts TagAddBlock TagDeployment TagOutgoingAct
    TagNonrecursiveCall TagRecursiveCall : core.

  Inductive ContractStepCase
      (contract : Contract Setup Msg State Error)
      (caddr : Address)
      (str : ChainStream)
      (i : nat) : Type :=
  | StepAddBlock :
      forall (header : BlockHeader)
             (queue_nil : chain_state_queue (CStr_nth i str) = [])
             (is_valid : IsValidNextBlock header (CStr_nth i str))
             (from_accs : Forall act_is_from_account (chain_state_queue (CStr_nth (S i) str)))
             (origin_acts : Forall act_origin_is_eq_from (chain_state_queue (CStr_nth (S i) str)))
             (env_eq : EnvironmentEquiv (CStr_nth (S i) str) (add_new_block_to_env header (CStr_nth i str)))
             (dep_info_eq : deployment_info Setup (CStr_clist str (S i)) caddr = deployment_info Setup (CStr_clist str i) caddr)
             (inc_calls_eq : incoming_calls Msg (CStr_clist str (S i)) caddr = incoming_calls Msg (CStr_clist str i) caddr)
             (out_txs_eq : outgoing_txs (CStr_clist str (S i)) caddr = outgoing_txs (CStr_clist str i) caddr),
        ContractStepCase contract caddr str i
  | StepDeployment :
      forall (ctx : ContractCallContext) (setup : Setup) (state : State)
             (ctx_addr : ctx.(ctx_contract_address) = caddr)
             (undeployed : env_contracts (CStr_nth i str) caddr = None)
             (init_some : init contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth i str)) ctx setup = Ok state)
             (env_eq : EnvironmentEquiv (CStr_nth (S i) str)
                         (set_contract_state caddr (serialize state)
                            (add_contract caddr contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth i str)))))
             (dep_info_eq : deployment_info Setup (CStr_clist str (S i)) caddr = Some (build_deployment_info ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) setup))
             (inc_calls_eq : incoming_calls Msg (CStr_clist str (S i)) caddr = incoming_calls Msg (CStr_clist str i) caddr)
             (out_txs_eq : outgoing_txs (CStr_clist str (S i)) caddr = outgoing_txs (CStr_clist str i) caddr)
             (inc_calla_nil : incoming_calls Msg (CStr_clist str i) caddr = Some [])
             (out_txs_nil : outgoing_txs (CStr_clist str i) caddr = []),
        ContractStepCase contract caddr str i
  | StepOutgoingAct :
      forall (out_act : ActionBody) (out_acts : list ActionBody) (prev_out_txs : list Tx) (tx : Tx)
             (outgoing_before : outgoing_acts (CStr_nth i str) caddr = out_act :: out_acts)
             (outgoing_after : outgoing_acts (CStr_nth (S i) str) caddr = out_acts)
             (outgoing_txs_before : outgoing_txs (CStr_clist str i) caddr = prev_out_txs)
             (outgoing_txs_after : outgoing_txs (CStr_clist str (S i)) caddr = tx :: prev_out_txs)
             (tx_from_caddr : tx_from tx = caddr)
             (tx_amount_eq : tx_amount tx = act_body_amount out_act)
             (tx_act_match :
                match out_act with
                | act_transfer to amount => tx_to tx = to /\ tx_amount tx = amount /\ (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
                | act_deploy amount wc setup => tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
                | act_call to amount msg => tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg)
                end)
             (chain_eq : (CStr_nth (S i) str : Chain) = (CStr_nth i str))
             (dep_info_eq : deployment_info Setup (CStr_clist str (S i)) caddr = deployment_info Setup (CStr_clist str i) caddr)
             (inc_calls_eq : incoming_calls Msg (CStr_clist str (S i)) caddr = incoming_calls Msg (CStr_clist str i) caddr)
             (cstate : State)
             (deployed_cstate_prev : contract_state (CStr_nth i str) caddr = Some cstate)
             (deployed_cstate_next : contract_state (CStr_nth (S i) str) caddr = Some cstate)
             ,
        ContractStepCase contract caddr str i
  | StepNonrecursiveCall :
      forall (ctx : ContractCallContext) (prev_state : State) (msg : option Msg)
             prev_inc
             (new_state : State) (new_acts : list ActionBody)
             (ctx_addr : ctx.(ctx_contract_address) = caddr)
             (from_other : ctx.(ctx_from) <> ctx.(ctx_contract_address))
             (deployed_cstate : contract_state (CStr_nth i str) caddr = Some prev_state)
             (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth i str)) ctx prev_state msg = Ok (new_state, new_acts))
             (env_eq : EnvironmentEquiv (CStr_nth (S i) str)
                         (set_contract_state caddr (serialize new_state) (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth i str))))
             (dep_info_eq : deployment_info Setup (CStr_clist str (S i)) caddr
                = deployment_info Setup (CStr_clist str i) caddr)
             (prev_inc_calls_some :  incoming_calls Msg (CStr_clist str i) caddr = Some prev_inc)
             (inc_calls_eq : incoming_calls Msg (CStr_clist str (S i)) caddr
                = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) msg :: prev_inc))
             (out_txs_eq : outgoing_txs (CStr_clist str (S i)) caddr = outgoing_txs (CStr_clist str i) caddr),
        ContractStepCase contract caddr str i
  | StepRecursiveCall :
      forall (ctx : ContractCallContext) (prev_state : State) (msg : option Msg)
             head prev_inc
             (new_state : State) (new_acts : list ActionBody)
             (ctx_addr : ctx.(ctx_contract_address) = caddr)
             (from_self : ctx.(ctx_from) = ctx.(ctx_contract_address))
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
             (deployed_cstate : contract_state (CStr_nth i str) caddr = Some prev_state)
             (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth i str)) ctx prev_state msg = Ok (new_state, new_acts))
             (env_eq : EnvironmentEquiv (CStr_nth (S i) str) (set_contract_state caddr (serialize new_state) (CStr_nth i str)))
             (dep_info_eq : deployment_info Setup (CStr_clist str (S i)) caddr = deployment_info Setup (CStr_clist str i) caddr)
             (prev_inc_calls_some : incoming_calls Msg (CStr_clist str i) caddr = Some prev_inc)
             (inc_calls_eq : incoming_calls Msg (CStr_clist str (S i)) caddr
                = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) msg :: prev_inc))
             (out_txs_eq : outgoing_txs (CStr_clist str (S i)) caddr
                = build_tx ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount)
                    (tx_call (match head with
                            | act_call _ _ msg => Some msg
                            | _ => None
                            end)) ::  outgoing_txs (CStr_clist str i) caddr),
        ContractStepCase contract caddr str i
  | StepIrrelevant :
      contract_view_unchanged contract caddr str i ->
        ContractStepCase contract caddr str i.

  Ltac solve_irrelevant_contract_view :=
    eapply StepIrrelevant;
    unfold contract_view_unchanged;
    cbn;
    repeat rewrite_environment_equiv;
    repeat split; cbn in *; eauto; try congruence.

  Lemma contract_step_case_complete_focused
      (contract : Contract Setup Msg State Error)
      (caddr : Address)
      (str : ChainStream)
      (start : CStr_nth 0 str = empty_state) :
    address_is_contract caddr = true ->
    forall i,
      env_contracts (CStr_nth (S i) str) caddr = Some (contract : WeakContract) ->
      inhabited (ContractStepCase contract caddr str i).
  Proof.
    intros Haddr * Henv_next.
    remember (CStr_link str i) as step eqn:Hstep.
    assert (HtraceS : CStr_clist str (S i) = snoc (CStr_clist str i) step)
      by (rewrite Hstep; apply CStr_clist_snoc).
    destruct_chain_step.
    - constructor; eapply StepAddBlock; eauto.
      all: expose_next_trace; auto.
    - (* step_action_user *)
      destruct (address_eqb_spec act.(act_from) caddr) as [|from_neq].
      {
        subst caddr. cbn in *.
        unfold act_is_from_account in from_acc.
        cbn in from_acc. congruence.
      }
      destruct_action_eval; subst act; cbn in from_neq.
      + (* transfer *)
        destruct (address_eqb_spec to_addr caddr) as [->|to_neq].
        {
          cbn in *.
          unfold act_is_from_account in from_acc.
          cbn in from_acc. congruence.
        }
        constructor; eapply StepIrrelevant.
        unfold contract_view_unchanged.
        repeat rewrite_environment_equiv.
        cbn in Henv_next.
        rewrite HtraceS. cbn.
        repeat (rewrite address_eq_ne; auto).
        repeat (split; auto).
        unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
        rewrite address_eq_ne; auto.
      + (* deploy *)
        destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
        * assert (wc_eq : wc = contract).
          { rewrite_environment_equiv. cbn in Henv_next.
            rewrite address_eq_refl in Henv_next.
            injection Henv_next as ->. reflexivity. }
          subst wc.
          specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
            eauto.
          constructor;
          eapply StepDeployment with
            (ctx := {|
              ctx_limit := limit;
              ctx_origin := origin;
              ctx_from := from_addr;
              ctx_contract_address := caddr;
              ctx_contract_balance := amount;
              ctx_amount := amount
              |}) ; eauto.
          subst; cbn in *. auto.
          assert (reach : reachable (CStr_nth (i) str)).
          { apply CStr_nth_reachable; auto. }
          all: try expose_next_trace; try rewrite address_eq_refl; auto.
          --
            now rewrite Hdeser.
          --
            rewrite address_eq_ne; auto.
          -- rewrite <- CStr_start_inc_calls_eq with (start := start).
            eapply undeployed_contract_no_in_calls; eauto.
          -- rewrite <- CStr_start_out_txs_eq with (start := start).
            eapply undeployed_contract_no_out_txs; eauto.

        * constructor; eapply StepIrrelevant.
          unfold contract_view_unchanged.
          repeat rewrite_environment_equiv.
          cbn in Henv_next. rewrite address_eq_ne in Henv_next; auto.
          rewrite HtraceS. cbn.
          repeat (rewrite address_eq_ne; auto).
          repeat (split; auto).
          unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
          rewrite address_eq_ne; auto.
      + (* call *)
        destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
        * assert (wc_eq : wc = contract).
          { rewrite_environment_equiv. cbn in Henv_next. rewrite deployed in *.
            injection Henv_next as ->. reflexivity. }
          subst wc.
          destruct (wc_receive_strong receive_some) as (prev_state_strong & msg_strong & new_state_strong & Hdeser_prev & Hdeser_msg & Hser_new & Hrecv).
          destruct (incoming_calls_typed (CStr_clist_start str start i) deployed) as (inc_calls & Hinc_calls).
          rewrite CStr_start_inc_calls_eq in Hinc_calls.
          constructor; eapply StepNonrecursiveCall; eauto.
          -- cbn; auto.
          -- cbn; auto.
          -- cbn. now rewrite deployed_state.
          -- subst. cbn in *; auto.
          -- expose_next_trace; auto.
          --
            expose_next_trace. rewrite address_eq_refl.
            destruct msg_strong.
            ++ cbn in Hdeser_msg. destruct msg; try congruence.
              rewrite Hdeser_msg. now rewrite Hinc_calls.
            ++ subst. now rewrite Hinc_calls.
          -- expose_next_trace; rewrite address_eq_ne; auto.
        * constructor; eapply StepIrrelevant.
          unfold contract_view_unchanged.
          repeat rewrite_environment_equiv.
          cbn in Henv_next.
          rewrite HtraceS. cbn.
          repeat (rewrite address_eq_ne; auto).
          repeat (split; auto).
          unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
          rewrite address_eq_ne; auto.
          rewrite filter_app, map_app, filter_build_act_from_ne; auto.
    - (* step_action_contract *)
      assert (reach : reachable (CStr_nth (i) str)).
      { apply CStr_nth_reachable; auto. }
      destruct_action_eval; subst act.
      + (* transfer *)
        destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
        * congruence.
        * (* outgoing acts *)
          destruct (address_eqb_spec from_addr caddr) as [-> | from_ne].
          -- (* out acts *)
            rewrite_environment_equiv. cbn in Henv_next.
            specialize (deployed_contract_state_typed Henv_next reach) as (cstate & deployed_state).
            constructor; eapply StepOutgoingAct with
               (out_act := act_transfer to_addr amount)
               (out_acts := outgoing_acts (CStr_nth (S i) str) caddr)
               (prev_out_txs := outgoing_txs (CStr_clist str i) caddr)
               (tx := build_tx limit origin caddr to_addr amount tx_empty); eauto.
             ++ unfold outgoing_acts; rewrite_queue; subst new_acts; cbn; rewrite address_eq_refl; reflexivity.
             ++ expose_next_trace; rewrite address_eq_refl; reflexivity.
             ++ rewrite_environment_equiv. auto.
             ++ expose_next_trace; auto.
             ++ expose_next_trace; auto.
             ++ rewrite_environment_equiv. auto.
          --
            constructor; eapply StepIrrelevant.
            unfold contract_view_unchanged.
            repeat rewrite_environment_equiv.
            cbn in Henv_next.
            rewrite HtraceS. cbn.
            repeat (rewrite address_eq_ne; auto).
            repeat (split; auto).
            unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
            rewrite address_eq_ne; auto.
      + (* deploy *)
        destruct (address_eqb_spec from_addr caddr) as [-> | from_ne];
        destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
        * (* recursive deploy is impossible *)
          rewrite_environment_equiv. cbn in Henv_next.
          rewrite address_eq_refl in Henv_next. inversion Henv_next; subst wc.
          specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
            eauto.
          specialize (undeployed_contract_no_out_queue caddr (CStr_nth i str) reach
            ltac:(auto) ltac:(auto))
            as no_out.
          rewrite_queue. apply Forall_cons_iff in no_out as (no_out & _).
          cbn in no_out. rewrite address_eq_refl in no_out; congruence.
        *
          rewrite_environment_equiv. cbn in Henv_next.
          rewrite address_eq_ne in Henv_next; auto.
          specialize (deployed_contract_state_typed Henv_next reach) as (cstate & deployed_state).
          constructor; eapply StepOutgoingAct with
               (out_act := act_deploy amount wc setup)
               (out_acts := outgoing_acts (CStr_nth (S i) str) caddr)
               (prev_out_txs := outgoing_txs (CStr_clist str i) caddr)
               (tx := build_tx limit origin caddr to_addr amount (tx_deploy wc setup)); eauto.
             -- unfold outgoing_acts; rewrite_queue; subst new_acts; cbn; rewrite address_eq_refl; reflexivity.
             -- expose_next_trace; rewrite address_eq_refl; reflexivity.
             -- rewrite_environment_equiv. auto.
             -- expose_next_trace; auto. rewrite address_eq_ne; auto.
             -- expose_next_trace; auto.
             -- rewrite_environment_equiv; cbn; rewrite address_eq_ne; auto.
        * (* deploy to us from other contract *)
          assert (wc_eq : wc = contract).
          { rewrite_environment_equiv. cbn in Henv_next.
            rewrite address_eq_refl in Henv_next.
            injection Henv_next as ->. reflexivity. }
          subst wc.
          destruct (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit).
          constructor; eapply StepDeployment; eauto.
          -- cbn. auto.
          -- subst. cbn in *; auto.
          -- expose_next_trace; auto. rewrite address_eq_refl, Hdeser; auto.
          -- expose_next_trace; auto.
          -- expose_next_trace; auto. rewrite address_eq_ne; auto.
          -- rewrite <- CStr_start_inc_calls_eq with (start := start). apply undeployed_contract_no_in_calls; auto.
          -- rewrite <- CStr_start_out_txs_eq with (start := start). apply undeployed_contract_no_out_txs; auto.
        * constructor; eapply StepIrrelevant.
          unfold contract_view_unchanged.
          repeat rewrite_environment_equiv.
          cbn in Henv_next. rewrite address_eq_ne in Henv_next; auto.
          rewrite HtraceS. cbn.
          repeat (rewrite address_eq_ne; auto).
          repeat (split; auto).
          unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
          rewrite address_eq_ne; auto.
      + (* call *)
        destruct (address_eqb_spec from_addr caddr) as [-> | from_ne];
        destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
        * (* recursive call *)
          assert (wc_eq : wc = contract).
          { rewrite_environment_equiv. cbn in Henv_next. rewrite deployed in Henv_next.
            injection Henv_next as ->. reflexivity. }
          subst wc.
          destruct (wc_receive_strong receive_some) as (prev_state_strong & msg_strong & new_state_strong & Hdeser_prev & Hdeser_msg & Hser_new & Hrecv).
          destruct (incoming_calls_typed (CStr_clist_start str start i) deployed) as (inc_calls & Hinc_calls).
          rewrite CStr_start_inc_calls_eq in Hinc_calls.
          constructor; eapply StepRecursiveCall
            with (head := match msg with
            | Some msg => act_call caddr amount msg
            | None => act_transfer caddr amount
            end); eauto.
          -- cbn; auto.
          -- cbn; auto.
          -- destruct msg_strong.
            ++ cbn in Hdeser_msg. destruct msg; try congruence.
              rewrite Hdeser_msg. cbn. repeat (split; auto).
            ++ subst. cbn. tauto.
          -- cbn. now rewrite deployed_state.
          -- rewrite_environment_equiv; rewrite Hser_new; cbn.
            now rewrite transfer_balance_same_addr_equiv.
          -- expose_next_trace; auto.
          --
            expose_next_trace. rewrite address_eq_refl.
            destruct msg_strong.
            ++ cbn in Hdeser_msg. destruct msg; try congruence.
              rewrite Hdeser_msg. now rewrite Hinc_calls.
            ++ subst. now rewrite Hinc_calls.
          -- expose_next_trace; auto. rewrite address_eq_refl. intros.
            subst. unfold outgoing_txs. auto.
            destruct msg_strong.
            ++ cbn in Hdeser_msg. destruct msg; try congruence.
            ++ subst. auto.
        * (* outgoing call *)
          rewrite_environment_equiv. cbn in Henv_next.
          specialize (deployed_contract_state_typed Henv_next reach) as (cstate & deployed_cstate).
          destruct msg as [msg_some|].
          -- constructor; eapply StepOutgoingAct with
            (out_act := act_call to_addr amount msg_some)
            (out_acts := outgoing_acts (CStr_nth (S i) str) caddr)
            (prev_out_txs := outgoing_txs (CStr_clist str i) caddr)
            (tx := build_tx limit origin caddr to_addr amount (tx_call (Some msg_some))); eauto.
            ++ unfold outgoing_acts; rewrite_queue; subst new_acts; cbn; rewrite address_eq_refl.
              cbn. rewrite filter_app, filter_build_act_from_ne; auto.
            ++ expose_next_trace; rewrite address_eq_refl; reflexivity.
            ++ rewrite_environment_equiv. auto.
            ++ expose_next_trace; auto.
            ++ expose_next_trace; auto. rewrite address_eq_ne; auto.
            ++ rewrite_environment_equiv; cbn; rewrite address_eq_ne; auto.
          -- constructor; eapply StepOutgoingAct with
               (out_act := act_transfer to_addr amount)
               (out_acts := outgoing_acts (CStr_nth (S i) str) caddr)
               (prev_out_txs := outgoing_txs (CStr_clist str i) caddr)
               (tx := build_tx limit origin caddr to_addr amount (tx_call None)); eauto.
             ++ unfold outgoing_acts; rewrite_queue; subst new_acts; cbn; rewrite address_eq_refl;
              cbn; rewrite filter_app, filter_build_act_from_ne; auto.
             ++ expose_next_trace; rewrite address_eq_refl. unfold outgoing_txs. reflexivity.
             ++ rewrite_environment_equiv. auto.
             ++ expose_next_trace; auto.
             ++ expose_next_trace; auto. rewrite address_eq_ne; auto.
             ++ rewrite_environment_equiv; cbn; rewrite address_eq_ne; auto.
        * (* nonrecursive call from other contract *)
          assert (wc_eq : wc = contract).
          { rewrite_environment_equiv. cbn in Henv_next. rewrite deployed in *.
            injection Henv_next as ->. reflexivity. }
          subst wc.
          destruct (wc_receive_strong receive_some) as (prev_state_strong & msg_strong & new_state_strong & Hdeser_prev & Hdeser_msg & Hser_new & Hrecv).
          destruct (incoming_calls_typed (CStr_clist_start str start i) deployed) as (inc_calls & Hinc_calls).
          rewrite CStr_start_inc_calls_eq in Hinc_calls.
          constructor; eapply StepNonrecursiveCall; eauto.
          -- cbn; auto.
          -- cbn; auto.
          -- cbn. now rewrite deployed_state.
          -- subst. cbn in *; auto.
          -- expose_next_trace; auto.
          --
            expose_next_trace. rewrite address_eq_refl.
            destruct msg_strong.
            ++ cbn in Hdeser_msg. destruct msg; try congruence.
              rewrite Hdeser_msg. now rewrite Hinc_calls.
            ++ subst. now rewrite Hinc_calls.
          -- expose_next_trace; rewrite address_eq_ne; auto.
        * constructor; eapply StepIrrelevant.
          unfold contract_view_unchanged.
          repeat rewrite_environment_equiv.
          cbn in Henv_next.
          rewrite HtraceS. cbn.
          repeat (rewrite address_eq_ne; auto).
          repeat (split; auto).
          unfold outgoing_acts. rewrite_queue. subst new_acts. cbn.
          rewrite address_eq_ne; auto.
          rewrite filter_app, map_app, filter_build_act_from_ne; auto.
    - (* step_action_invalid *)

      (* destruct (address_eqb_spec (act_from act) caddr) as [<- | from_ne].
      + exfalso.
        assert (reach : reachable (CStr_nth i str)).
        { apply CStr_nth_reachable; auto. }
        assert (from_contract : act_is_from_contract act).
        { unfold act_is_from_contract. exact Haddr. }
        destruct
          (action_fail_false_contract_head_absurd
             (CStr_nth i str) act acts reach queue_prev from_contract)
          as (finish_bstate & [trace_finish] & queue_finish).
          eapply action_trace_finish_fail_absurd
            with (st := CStr_nth i str)
                  (finish := finish_bstate)
                  (fail := fail_bstate)
                  (act := act)
                  (acts := list_drop_contract_action acts)
                  (act' := act')
                  (acts' := acts'); eauto. *)

      destruct (address_eqb_spec (act_from act) caddr) as [<- | from_ne].
      + (* from contract *) (* contra *)
        exfalso.
        assert (reach : reachable (CStr_nth i str)).
        { apply CStr_nth_reachable; auto. }
        assert (from_contract : act_is_from_contract act).
        { unfold act_is_from_contract. exact Haddr. }
        destruct
          (action_fail_false_contract_head_absurd
             (CStr_nth i str) act acts reach queue_prev from_contract)
          as (finish_bstate & [trace_finish] & queue_finish).
        assert (target_account :
          Forall act_is_from_account (list_drop_contract_action acts)).
        {
          pose proof
            (reachable_list_drop_contract_action_queue
               (CStr_nth i str) reach)
            as Hdrop.
          rewrite queue_prev in Hdrop.
          cbn in Hdrop.
          unfold act_is_from_contract in from_contract.
          rewrite from_contract in Hdrop.
          exact Hdrop.
        }
        eapply action_trace_finish_fail_absurd_general
              with (st := CStr_nth i str)
                   (finish := finish_bstate)
                   (fail := fail_bstate)
                   (target := list_drop_contract_action acts); eauto.
      + (* irrelevant *)
        constructor; eapply StepIrrelevant.
        unfold contract_view_unchanged.
        repeat rewrite_environment_equiv.
        cbn in Henv_next.
        rewrite HtraceS. cbn.
        repeat (rewrite address_eq_ne; auto).
        repeat (split; auto).
        unfold outgoing_acts. rewrite_queue. cbn.
        rewrite address_eq_ne; auto.
  Qed.

  Lemma solve_G
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (start : CStr_nth 0 str = empty_state) (f : formula) :

    forall i,

    satisfies contract caddr str i f ->

    (* AddBlock *)
    (forall (j : nat) (Hij : (i <= j)%nat) (header : BlockHeader)
            (queue_nil : chain_state_queue (CStr_nth j str) = [])
            (is_valid : IsValidNextBlock header (CStr_nth j str))
            (from_accs : Forall act_is_from_account (chain_state_queue (CStr_nth (S j) str)))
            (origin_acts : Forall act_origin_is_eq_from (chain_state_queue (CStr_nth (S j) str)))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (add_new_block_to_env header (CStr_nth j str)))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f) (tag : TagAddBlock),
        satisfies contract caddr str (S j) f) ->

    (* Deploy *)
    (forall (j : nat) (Hij : (i <= j)%nat) ctx setup state
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (undeployed : env_contracts (CStr_nth j str) caddr = None)
            (init_some : init contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth j str)) ctx setup = Ok state)
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize state) (add_contract caddr contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth j str)))))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = Some (build_deployment_info ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) setup))
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (inc_calla_nil : incoming_calls Msg (CStr_clist str j) caddr = Some [])
            (out_txs_nil : outgoing_txs (CStr_clist str j) caddr = [])
            (IH : satisfies contract caddr str j f) (tag : TagDeployment),
        satisfies contract caddr str (S j) f) ->

    (* Outgoing *)
    (forall (j : nat) (Hij : (i <= j)%nat) (out_act : ActionBody) (tx : Tx)
            (tx_from_caddr : tx_from tx = caddr)
            (tx_amount_eq : tx_amount tx = act_body_amount out_act)
            (tx_act_match : match out_act with
               | act_transfer to amount => tx_to tx = to /\ tx_amount tx = amount /\ (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
               | act_deploy amount wc setup => tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
               | act_call to amount msg => tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg) end)
            (chain_eq : (CStr_nth (S j) str : Chain) = (CStr_nth j str : Chain))
            (out_acts_eq : outgoing_acts (CStr_nth j str) caddr = out_act :: outgoing_acts (CStr_nth (S j) str) caddr)
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr =
                tx :: outgoing_txs (CStr_clist str j) caddr)
            (deployed_prev : env_contracts (CStr_nth j str) caddr = Some (contract : WeakContract))
            (cstate : State)
            (deployed_cstate_prev : contract_state (CStr_nth j str) caddr = Some cstate)
            (deployed_cstate_next : contract_state (CStr_nth (S j) str) caddr = Some cstate)
            (IH : satisfies contract caddr str j f) (tag : TagOutgoingAct),
        satisfies contract caddr str (S j) f) ->

    (* Nonrecursive Call *)
    (forall (j : nat) (Hij : (i <= j)%nat) ctx prev_state msg prev_inc new_state new_acts
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (from_other : ctx.(ctx_from) <> ctx.(ctx_contract_address))
            (deployed_cstate : contract_state (CStr_nth j str) caddr = Some prev_state)
            (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str)) ctx prev_state msg = Ok (new_state, new_acts))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize new_state) (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str))))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (prev_inc_calls_some :  incoming_calls Msg (CStr_clist str j) caddr = Some prev_inc)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr
               = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) msg :: prev_inc))
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f)
            (tag : TagNonrecursiveCall),
        satisfies contract caddr str (S j) f) ->

    (* Recursive Call *)
    (forall (j : nat) (Hij : (i <= j)%nat) (ctx : ContractCallContext) (prev_state : State) (msg : option Msg)
            head prev_inc
            (new_state : State) (new_acts : list ActionBody)
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (from_self : ctx.(ctx_from) = ctx.(ctx_contract_address))
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
            (deployed_cstate : contract_state (CStr_nth j str) caddr = Some prev_state)
            (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str)) ctx prev_state msg = Ok (new_state, new_acts))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize new_state) (CStr_nth j str)))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (prev_inc_calls_some : incoming_calls Msg (CStr_clist str j) caddr = Some prev_inc)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr
               = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
                        ctx.(ctx_amount) msg :: prev_inc))
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr
               = build_tx ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount)
                  (tx_call (match head with
                            | act_call _ _ msg => Some msg
                            | _ => None
                            end)) ::  outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f)
            (tag : TagRecursiveCall),
        satisfies contract caddr str (S j) f) ->

    (forall (j : nat) (Hij : (i <= j)%nat),
        x_free f = false ->
        contract_view_unchanged contract caddr str j ->
        satisfies contract caddr str j f -> satisfies contract caddr str (S j) f) ->

    (forall (j : nat) (Hij : (i <= j)%nat),
        x_free f = false ->
        env_contracts (CStr_nth j str) caddr <> Some (contract : WeakContract) ->
        env_contracts (CStr_nth (S j) str) caddr <> Some (contract : WeakContract) ->
        satisfies contract caddr str j f -> satisfies contract caddr str (S j) f) ->

    satisfies contract caddr str i (ltl_G f).
  Proof.
    intros i.
    intros start_case
           add_block_case
           init_case
           outgoing_act_case
           nonrecursive_call_case
           recursive_call_case
           irrelevant_x_case undeployed_x_case.
    assert (step_preserves : forall n,
      i <= n ->
      satisfies contract caddr str n f ->
      satisfies contract caddr str (S n) f).
    {
      intros n Hin IH.
      destruct (env_contracts (CStr_nth n str) caddr)
        as [wc|] eqn:deployed;
      [destruct (weakcontract_decidability wc contract) as [->|]|].
      2: {
        assert (Hnot_now :
          env_contracts (CStr_nth n str) caddr <>
          Some (contract : WeakContract)) by congruence.
        assert (Hnot_next :
          env_contracts (CStr_nth (S n) str) caddr <>
          Some (contract : WeakContract)).
        {
          intro Htarget_next.
          pose proof (CStr_wc_preserve str deployed (S n) ltac:(lia))
            as Hwc_next.
          congruence.
        }
        destruct (x_free f) eqn:Hxf;
          [eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
      }
      - (* deployed *)
        specialize (contract_addr_format caddr contract (CStr_nth_reachable str start n)
          deployed)
          as caddr_is_contract.
        assert (deployed_Sn : env_contracts (CStr_nth (S n) str) caddr = Some (contract : WeakContract)).
        { eapply CStr_wc_preserve; eauto.  }
        specialize (contract_step_case_complete_focused contract caddr str
          start caddr_is_contract n ltac:(auto)) as [cstep].
        destruct cstep;
          [ eapply add_block_case; eauto
          | try congruence
          | eapply outgoing_act_case; eauto
          | eapply nonrecursive_call_case; eauto
          | eapply recursive_call_case; eauto
          | destruct (x_free f) eqn:Hxf;
            [eapply satis_equiv_forward; eauto | eapply irrelevant_x_case; eauto] ].
        + (* outgoing_act_case *)
          now rewrite outgoing_before, outgoing_after.
        + (* outgoing_act_case *)
          now rewrite outgoing_txs_before, outgoing_txs_after.
      - (* undeployd *)
        destruct (env_contracts (CStr_nth (S n) str) caddr)
          as [wc|] eqn:deployed_Sn;
        [destruct (weakcontract_decidability wc contract) as [->|]|].
        2: {
          assert (Hnot_now :
            env_contracts (CStr_nth n str) caddr <>
            Some (contract : WeakContract)) by congruence.
          assert (Hnot_next :
            env_contracts (CStr_nth (S n) str) caddr <>
            Some (contract : WeakContract)) by congruence.
          destruct (x_free f) eqn:Hxf;
          [eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
        }
        2: {
          assert (Hnot_now :
            env_contracts (CStr_nth n str) caddr <>
            Some (contract : WeakContract)) by congruence.
          assert (Hnot_next :
            env_contracts (CStr_nth (S n) str) caddr <>
            Some (contract : WeakContract)) by congruence.
          destruct (x_free f) eqn:Hxf;
          [eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
        }
        specialize (contract_addr_format caddr contract (CStr_nth_reachable str start (S n))
          ltac:(auto))
            as caddr_is_contract.
        remember (CStr_link str n) as step eqn:Hstep.
        assert (HtraceS : CStr_clist str (S n) = snoc (CStr_clist str n) step)
          by (rewrite Hstep; apply CStr_clist_snoc).
        destruct_chain_step; [ |destruct_action_eval | destruct_action_eval | ];
          rewrite_environment_equiv;
          cbn in deployed; cbn in deployed_Sn; try congruence.
        + (* user_action *)
          destruct (address_eqb_spec act.(act_from) caddr) as [|from_neq].
          {
            subst caddr. cbn in *.
            unfold act_is_from_account in from_acc.
            cbn in from_acc. congruence.
          }
          subst act.
          destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
          * assert (wc_eq : wc = contract).
            { rewrite_environment_equiv. cbn in deployed_Sn.
              rewrite address_eq_refl in deployed_Sn.
              injection deployed_Sn as ->. reflexivity. }
            subst wc.
            specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
              eauto.
            eapply init_case; eauto.
            -- auto.
            -- rewrite_environment_equiv. cbn.
              rewrite Hser. reflexivity.
            -- expose_next_trace. rewrite address_eq_refl, Hdeser; auto.
            -- expose_next_trace; auto.
            -- expose_next_trace; auto. rewrite address_eq_ne; auto.
            -- rewrite <- CStr_start_inc_calls_eq with (start := start); apply undeployed_contract_no_in_calls; auto.
            -- rewrite <- CStr_start_out_txs_eq with (start := start); apply undeployed_contract_no_out_txs; auto.
          * exfalso.
            rewrite_environment_equiv. cbn in deployed_Sn.
            rewrite address_eq_ne in deployed_Sn; auto.
            congruence.
        + (* contract action *)
          subst act.
          destruct (address_eqb_spec from_addr caddr) as [-> | from_ne];
          destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
          * rewrite_environment_equiv.
            specialize (CStr_nth_reachable str start n) as reach.
            specialize (undeployed_contract_no_out_queue caddr (CStr_nth n str) reach
              ltac:(auto) ltac:(auto))
              as no_out.
            rewrite_queue. apply Forall_cons_iff in no_out as (no_out & _).
            cbn in no_out. rewrite address_eq_refl in no_out; congruence.
          * rewrite_environment_equiv.
            specialize (CStr_nth_reachable str start n) as reach.
            specialize (undeployed_contract_no_out_queue caddr (CStr_nth n str) reach
              ltac:(auto) ltac:(auto))
              as no_out.
            rewrite_queue. apply Forall_cons_iff in no_out as (no_out & _).
            cbn in no_out. rewrite address_eq_refl in no_out; congruence.
          * assert (wc_eq : wc = contract).
            { rewrite_environment_equiv. cbn in deployed_Sn.
              rewrite address_eq_refl in deployed_Sn.
              injection deployed_Sn as ->. reflexivity. }
            subst wc.
            specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
              eauto.
            eapply init_case; eauto.
            -- auto.
            -- rewrite_environment_equiv. cbn.
              rewrite Hser. reflexivity.
            -- expose_next_trace. rewrite address_eq_refl, Hdeser; auto.
            -- expose_next_trace; auto.
            -- expose_next_trace; auto. rewrite address_eq_ne; auto.
            -- rewrite <- CStr_start_inc_calls_eq with (start := start); apply undeployed_contract_no_in_calls; auto.
            -- rewrite <- CStr_start_out_txs_eq with (start := start); apply undeployed_contract_no_out_txs; auto.
          * exfalso.
            rewrite_environment_equiv. cbn in deployed_Sn.
            rewrite address_eq_ne in deployed_Sn; auto.
            congruence.
    }
    intros j. remember (j - i)%nat as d.
    generalize dependent j. induction d as [|d IHd].
    - intros.
      assert (i = j) by lia; now subst i.
    - intros * Hd Hij.
      destruct j as [|j']; [lia|].
      apply step_preserves; auto.
      lia.
      apply IHd; lia.
  Qed.

  Lemma solve_step
      (contract : Contract Setup Msg State Error) (caddr : Address)
      (str : ChainStream) (start : CStr_nth 0 str = empty_state) (f g : formula) :

    forall i,

    (* AddBlock *)
    (forall (j : nat) (Hij : (i <= j)%nat) (header : BlockHeader)
            (queue_nil : chain_state_queue (CStr_nth j str) = [])
            (is_valid : IsValidNextBlock header (CStr_nth j str))
            (from_accs : Forall act_is_from_account (chain_state_queue (CStr_nth (S j) str)))
            (origin_acts : Forall act_origin_is_eq_from (chain_state_queue (CStr_nth (S j) str)))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (add_new_block_to_env header (CStr_nth j str)))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f) (tag : TagAddBlock),
        satisfies contract caddr str (S j) g) ->

    (* Deploy *)
    (forall (j : nat) (Hij : (i <= j)%nat) ctx setup state
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (undeployed : env_contracts (CStr_nth j str) caddr = None)
            (init_some : init contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth j str)) ctx setup = Ok state)
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize state) (add_contract caddr contract (transfer_balance ctx.(ctx_from) caddr ctx.(ctx_amount) (CStr_nth j str)))))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = Some (build_deployment_info ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) setup))
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (inc_calla_nil : incoming_calls Msg (CStr_clist str j) caddr = Some [])
            (out_txs_nil : outgoing_txs (CStr_clist str j) caddr = [])
            (IH : satisfies contract caddr str j f) (tag : TagDeployment),
        satisfies contract caddr str (S j) g) ->

    (* Outgoing *)
    (forall (j : nat) (Hij : (i <= j)%nat) (out_act : ActionBody) (tx : Tx)
            (tx_from_caddr : tx_from tx = caddr)
            (tx_amount_eq : tx_amount tx = act_body_amount out_act)
            (tx_act_match : match out_act with
               | act_transfer to amount => tx_to tx = to /\ tx_amount tx = amount /\ (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
               | act_deploy amount wc setup => tx_amount tx = amount /\ tx_body tx = tx_deploy wc setup
               | act_call to amount msg => tx_to tx = to /\ tx_amount tx = amount /\ tx_body tx = tx_call (Some msg) end)
            (chain_eq : (CStr_nth (S j) str : Chain) = (CStr_nth j str : Chain))
            (out_acts_eq : outgoing_acts (CStr_nth j str) caddr = out_act :: outgoing_acts (CStr_nth (S j) str) caddr)
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr = incoming_calls Msg (CStr_clist str j) caddr)
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr =
                tx :: outgoing_txs (CStr_clist str j) caddr)
            (deployed_prev : env_contracts (CStr_nth j str) caddr = Some (contract : WeakContract))
            (cstate : State)
            (deployed_cstate_prev : contract_state (CStr_nth j str) caddr = Some cstate)
            (deployed_cstate_next : contract_state (CStr_nth (S j) str) caddr = Some cstate)
            (IH : satisfies contract caddr str j f) (tag : TagOutgoingAct),
        satisfies contract caddr str (S j) g) ->

    (* Nonrecursive Call *)
    (forall (j : nat) (Hij : (i <= j)%nat) ctx prev_state msg prev_inc new_state new_acts
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (from_other : ctx.(ctx_from) <> ctx.(ctx_contract_address))
            (deployed_cstate : contract_state (CStr_nth j str) caddr = Some prev_state)
            (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str)) ctx prev_state msg = Ok (new_state, new_acts))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize new_state) (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str))))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (prev_inc_calls_some :  incoming_calls Msg (CStr_clist str j) caddr = Some prev_inc)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr
               = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) msg :: prev_inc))
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr = outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f)
            (tag : TagNonrecursiveCall),
        satisfies contract caddr str (S j) g) ->

    (* Recursive Call *)
    (forall (j : nat) (Hij : (i <= j)%nat) (ctx : ContractCallContext) (prev_state : State) (msg : option Msg)
            head prev_inc
            (new_state : State) (new_acts : list ActionBody)
            (ctx_addr : ctx.(ctx_contract_address) = caddr)
            (from_self : ctx.(ctx_from) = ctx.(ctx_contract_address))
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
            (deployed_cstate : contract_state (CStr_nth j str) caddr = Some prev_state)
            (receive_some : receive contract (transfer_balance ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount) (CStr_nth j str)) ctx prev_state msg = Ok (new_state, new_acts))
            (env_eq : EnvironmentEquiv (CStr_nth (S j) str) (set_contract_state caddr (serialize new_state) (CStr_nth j str)))
            (dep_info_eq : deployment_info Setup (CStr_clist str (S j)) caddr = deployment_info Setup (CStr_clist str j) caddr)
            (prev_inc_calls_some : incoming_calls Msg (CStr_clist str j) caddr = Some prev_inc)
            (inc_calls_eq : incoming_calls Msg (CStr_clist str (S j)) caddr
               = Some (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
                        ctx.(ctx_amount) msg :: prev_inc))
            (out_txs_eq : outgoing_txs (CStr_clist str (S j)) caddr
               = build_tx ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_contract_address) ctx.(ctx_amount)
                  (tx_call (match head with
                            | act_call _ _ msg => Some msg
                            | _ => None
                            end)) ::  outgoing_txs (CStr_clist str j) caddr)
            (IH : satisfies contract caddr str j f)
            (tag : TagRecursiveCall),
        satisfies contract caddr str (S j) g) ->

    (forall (j : nat) (Hij : (i <= j)%nat),
        satisfies contract caddr str j f -> satisfies contract caddr str j g) ->

    (forall (j : nat) (Hij : (i <= j)%nat),
        x_free f = false ->
        contract_view_unchanged contract caddr str j ->
        satisfies contract caddr str j f -> satisfies contract caddr str (S j) g) ->

    (forall (j : nat) (Hij : (i <= j)%nat),
        x_free f = false ->
        env_contracts (CStr_nth j str) caddr <> Some (contract : WeakContract) ->
        env_contracts (CStr_nth (S j) str) caddr <> Some (contract : WeakContract) ->
        satisfies contract caddr str j f -> satisfies contract caddr str (S j) g) ->

    forall n, (i <= n)%nat ->
      satisfies contract caddr str n f ->
      satisfies contract caddr str (S n) g.
  Proof.
    intros i.
    intros add_block_case
           init_case
           outgoing_act_case
           nonrecursive_call_case
           recursive_call_case
           f_impl_g
           irrelevant_x_case undeployed_x_case.
      intros n Hin IH.
      destruct (env_contracts (CStr_nth n str) caddr)
        as [wc|] eqn:deployed;
      [destruct (weakcontract_decidability wc contract) as [->|]|].
      2: {
        assert (Hnot_now :
          env_contracts (CStr_nth n str) caddr <>
          Some (contract : WeakContract)) by congruence.
        assert (Hnot_next :
          env_contracts (CStr_nth (S n) str) caddr <>
          Some (contract : WeakContract)).
        {
          intro Htarget_next.
          pose proof (CStr_wc_preserve str deployed (S n) ltac:(lia))
            as Hwc_next.
          congruence.
        }
        destruct (x_free f) eqn:Hxf;
          [eapply f_impl_g; [lia|]; eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
      }
      - (* deployed *)
        specialize (contract_addr_format caddr contract (CStr_nth_reachable str start n)
          deployed)
          as caddr_is_contract.
        assert (deployed_Sn : env_contracts (CStr_nth (S n) str) caddr = Some (contract : WeakContract)).
        { eapply CStr_wc_preserve; eauto.  }
        specialize (contract_step_case_complete_focused contract caddr str
          start caddr_is_contract n ltac:(auto)) as [cstep].
        destruct cstep;
          [ eapply add_block_case; eauto
          | try congruence
          | eapply outgoing_act_case; eauto
          | eapply nonrecursive_call_case; eauto
          | eapply recursive_call_case; eauto
          | destruct (x_free f) eqn:Hxf;
            [eapply f_impl_g; [lia|]; eapply satis_equiv_forward; eauto | eapply irrelevant_x_case; eauto] ].
        + (* outgoing_act_case *)
          now rewrite outgoing_before, outgoing_after.
        + (* outgoing_act_case *)
          now rewrite outgoing_txs_before, outgoing_txs_after.
      - (* undeployd *)
        destruct (env_contracts (CStr_nth (S n) str) caddr)
          as [wc|] eqn:deployed_Sn;
        [destruct (weakcontract_decidability wc contract) as [->|]|].
        2: {
          assert (Hnot_now :
            env_contracts (CStr_nth n str) caddr <>
            Some (contract : WeakContract)) by congruence.
          assert (Hnot_next :
            env_contracts (CStr_nth (S n) str) caddr <>
            Some (contract : WeakContract)) by congruence.
          destruct (x_free f) eqn:Hxf;
          [eapply f_impl_g; [lia|]; eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
        }
        2: {
          assert (Hnot_now :
            env_contracts (CStr_nth n str) caddr <>
            Some (contract : WeakContract)) by congruence.
          assert (Hnot_next :
            env_contracts (CStr_nth (S n) str) caddr <>
            Some (contract : WeakContract)) by congruence.
          destruct (x_free f) eqn:Hxf;
          [eapply f_impl_g; [lia|]; eapply satis_not_deployed_forward; eauto | eapply undeployed_x_case; eauto].
        }
        specialize (contract_addr_format caddr contract (CStr_nth_reachable str start (S n))
          ltac:(auto))
            as caddr_is_contract.
        remember (CStr_link str n) as step eqn:Hstep.
        assert (HtraceS : CStr_clist str (S n) = snoc (CStr_clist str n) step)
          by (rewrite Hstep; apply CStr_clist_snoc).
        destruct_chain_step; [ |destruct_action_eval | destruct_action_eval | ];
          rewrite_environment_equiv;
          cbn in deployed; cbn in deployed_Sn; try congruence.
        + (* user_action *)
          destruct (address_eqb_spec act.(act_from) caddr) as [|from_neq].
          {
            subst caddr. cbn in *.
            unfold act_is_from_account in from_acc.
            cbn in from_acc. congruence.
          }
          subst act.
          destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
          * assert (wc_eq : wc = contract).
            { rewrite_environment_equiv. cbn in deployed_Sn.
              rewrite address_eq_refl in deployed_Sn.
              injection deployed_Sn as ->. reflexivity. }
            subst wc.
            specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
              eauto.
            eapply init_case; eauto.
            -- auto.
            -- rewrite_environment_equiv. cbn.
              rewrite Hser. reflexivity.
            -- expose_next_trace. rewrite address_eq_refl, Hdeser; auto.
            -- expose_next_trace; auto.
            -- expose_next_trace; auto. rewrite address_eq_ne; auto.
            -- rewrite <- CStr_start_inc_calls_eq with (start := start); apply undeployed_contract_no_in_calls; auto.
            -- rewrite <- CStr_start_out_txs_eq with (start := start); apply undeployed_contract_no_out_txs; auto.
          * exfalso.
            rewrite_environment_equiv. cbn in deployed_Sn.
            rewrite address_eq_ne in deployed_Sn; auto.
            congruence.
        + (* contract action *)
          subst act.
          destruct (address_eqb_spec from_addr caddr) as [-> | from_ne];
          destruct (address_eqb_spec to_addr caddr) as [-> | to_ne].
          * rewrite_environment_equiv.
            specialize (CStr_nth_reachable str start n) as reach.
            specialize (undeployed_contract_no_out_queue caddr (CStr_nth n str) reach
              ltac:(auto) ltac:(auto))
              as no_out.
            rewrite_queue. apply Forall_cons_iff in no_out as (no_out & _).
            cbn in no_out. rewrite address_eq_refl in no_out; congruence.
          * rewrite_environment_equiv.
            specialize (CStr_nth_reachable str start n) as reach.
            specialize (undeployed_contract_no_out_queue caddr (CStr_nth n str) reach
              ltac:(auto) ltac:(auto))
              as no_out.
            rewrite_queue. apply Forall_cons_iff in no_out as (no_out & _).
            cbn in no_out. rewrite address_eq_refl in no_out; congruence.
          * assert (wc_eq : wc = contract).
            { rewrite_environment_equiv. cbn in deployed_Sn.
              rewrite address_eq_refl in deployed_Sn.
              injection deployed_Sn as ->. reflexivity. }
            subst wc.
            specialize (wc_init_strong init_some) as (setup_strong & state_strong & Hdeser & Hser & Hinit);
              eauto.
            eapply init_case; eauto.
            -- auto.
            -- rewrite_environment_equiv. cbn.
              rewrite Hser. reflexivity.
            -- expose_next_trace. rewrite address_eq_refl, Hdeser; auto.
            -- expose_next_trace; auto.
            -- expose_next_trace; auto. rewrite address_eq_ne; auto.
            -- rewrite <- CStr_start_inc_calls_eq with (start := start); apply undeployed_contract_no_in_calls; auto.
            -- rewrite <- CStr_start_out_txs_eq with (start := start); apply undeployed_contract_no_out_txs; auto.
          * exfalso.
            rewrite_environment_equiv. cbn in deployed_Sn.
            rewrite address_eq_ne in deployed_Sn; auto.
            congruence.
  Qed.

End Solve_G.

End PathSemantics_G.

End LTL_G.

Ltac solve_G :=
  eapply solve_G;
  try (let Hxf := fresh "Hxf" in
       intros ? ? Hxf; vm_compute in Hxf; discriminate Hxf).
