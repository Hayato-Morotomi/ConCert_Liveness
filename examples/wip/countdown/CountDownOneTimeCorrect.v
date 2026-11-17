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
From Stdlib Require Import Lia.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream ChainStream.
From ConCert.Examples.Wip.LTL Require Import MyLTL. Import LTLNotation.
From ConCert.Examples.Wip.ExecutionModel Require Import MyBuildUtils.
From ConCert.Examples.Wip.CountDown Require Import CountDownOneTime.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics.

Section CountDownOneTimeCorrect.
  Context {BaseTypes : ChainBase}.

  Tactic Notation "contract_simpl" := repeat contract_simpl_step @CountDownOneTime.receive @CountDownOneTime.init.

Section FunctionalProperties.

  Lemma count_end_correct : forall chain ctx st new_st new_acts,
      receive chain ctx st (Some Fin) = Ok (new_st, new_acts) ->
      st.(count) = 0%nat /\
      st.(ended) = false /\
      new_st = st <| ended := true |> /\
      new_acts = [].
  Proof.
    intros * receive_some. contract_simpl. repeat (split; auto). lia.
  Qed.

  Lemma count_end_is_some : forall prev_state chain ctx,
    prev_state.(count) = 0%nat /\
    prev_state.(ended) = false
    <->
    exists new_st new_acts,
      receive chain ctx prev_state (Some Fin) = Ok (new_st, new_acts).
  Proof.
    split.
    - intros (? & ?). exists (prev_state <| ended := true |>), [].
      contract_simpl. lia.
    - intros (? & ? & ?).
      contract_simpl. split; [lia|auto].
  Qed.

  Lemma dec_decrements : forall chain ctx st new_st new_acts,
      receive chain ctx st (Some Dec) = Ok (new_st, new_acts) ->
      st.(ended) = false /\ new_st.(count) = (st.(count) - 1)%nat.
  Proof.
    intros * receive_some. contract_simpl. split; auto.
  Qed.

  (** A successful contract call never increases [count].
      This is used both by the global monotonicity proof and by the
      non-increase premise of [solve_U_eventually_decrease_spec]. *)
  Lemma contract_not_increase :
    forall chain ctx prev_state msg new_state new_acts,
      receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
      (new_state.(count) <= prev_state.(count))%nat.
  Proof.
    intros chain ctx prev_state msg new_state new_acts receive_some.
    destruct msg as [msg|]; [destruct msg|];
      contract_simpl;
      cbn in *;
      try congruence;
      lia.
  Qed.

End FunctionalProperties.

  Definition FinSeen
    : forall (chain_height current_slot finalized_height : nat)
            (caddr : Address)
            (dep_info : DeploymentInfo Setup)
            (cs : State)
            (balance : Amount)
            (out_acts : list ActionBody)
            (inc_calls : list (ContractCallInfo Msg))
            (out_txs : list Tx), Prop :=
    fun _ _ _ _ _ _ _ _ inc_calls _ =>
      exists limit origin from amount,
        List.In
          (build_call_info limit origin from amount (Some Fin))
          inc_calls.

  Definition CanFin
    : forall (chain_height current_slot finalized_height : nat)
            (caddr : Address)
            (dep_info : (DeploymentInfo Setup))
            (cs : State)
            (balance : Amount)
            (out_acts : list ActionBody)
            (inc_calls : (list (ContractCallInfo Msg)))
            (out_txs : list Tx), Prop :=
    fun chain_height current_slot finalized_height caddr
        _ cstate _ _ _ _ =>
      exists ctx new_cstate,
        receive
          (build_chain chain_height current_slot finalized_height)
          ctx
          cstate
          (Some Fin)
        = Ok (new_cstate, []).

Section SafetyProperties.

  Lemma ended_correct_orig caddr st :
    reachable st ->
    env_contracts st caddr = Some (contract : WeakContract) ->
    exists (cstate : State),
        contract_state st caddr = Some cstate /\
        (cstate.(count) <> 0%nat ->
         cstate.(ended) = false).
  Proof.
    contract_induction; intros; contract_simpl; auto.
    - destruct msg as [m|]; [destruct m|];
      contract_simpl;
      cbn in *; auto.
      + lia.
      + congruence.
    - destruct msg as [m|]; [destruct m|];
      contract_simpl;
      cbn in *; auto.
      + lia.
      + congruence.
    - solve_facts.
  Qed.

  (** [ltl_atom] itself is conditional on deployment.  Consequently the
      explicit formula [ltl_dep -> ...] from the option-valued semantics is
      redundant here and is removed. *)
  Lemma ended_correct caddr str
      (start : CStr_nth 0 str = empty_state) :
    let P := fun _ _ _ _
      (_ : DeploymentInfo Setup)
      (cstate : State)
      _ _
      (_ : list (ContractCallInfo Msg))
      _ =>
      cstate.(count) <> 0%nat ->
      cstate.(ended) = false
    in
    satisfies contract caddr str 0 (G (l_atom P)).
  Proof.
    cbn [satisfies].
    intros j _ deployed_j.
    cstr_destruct_deployed_typed.
    exists dep_info, cstate, inc_calls.
    repeat split; try assumption.
    destruct (ended_correct_orig caddr (CStr_nth j str)
      (CStr_nth_reachable str start j) deployed_j)
      as (cstate' & Hcstate' & Hended).
    rewrite Hcstate in Hcstate'.
    inversion Hcstate'; subst cstate'.
    exact Hended.
  Qed.

  Lemma ended_implies_fin_seen_orig bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists dep cstate inc_calls,
      deployment_info Setup trace caddr = Some dep /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      (cstate.(ended) = true ->
       exists limit origin from amount,
         In (build_call_info limit origin from amount (Some Fin)) inc_calls).
  Proof.
    contract_induction; intros; cbn in *; auto.
    - (* deployment: init sets ended := false *)
      contract_simpl. cbn in *. discriminate.
    - (* nonrecursive call: Dec needs ended = false, Fin is itself recorded *)
      destruct msg as [[|]|]; contract_simpl; cbn in *;
        try congruence; do 4 eexists; left; reflexivity.
    - (* recursive call *)
      destruct msg as [[|]|]; contract_simpl; cbn in *;
        try congruence; do 4 eexists; left; reflexivity.
    - solve_facts.
  Qed.

  Lemma end_not_seen_implies_not_ended caddr str (start : CStr_nth 0 str = empty_state) :
    satisfies contract caddr str 0
      (G ((l_not (l_atom FinSeen))
          l_impl
          (l_atom
            (fun _ _ _ _
              (_ : DeploymentInfo Setup)
              (cstate : State)
              _ _
              (_ : list (ContractCallInfo Msg))
              _ =>
                cstate.(ended) = false)))).
  Proof.
    cbn [satisfies].
    intros j _ Hnot_seen deployed_j.
    destruct (ended_implies_fin_seen_orig (CStr_nth j str) caddr
      (CStr_clist_start str start j) deployed_j)
      as (dep & cstate & inc & Hdep & Hcstate & Hinc & Hended).
    rewrite CStr_deploy_info_eq in Hdep.
    rewrite CStr_incoming_calls_eq in Hinc.
    exists dep, cstate, inc.
    repeat split; try assumption.
    destruct (ended cstate) eqn:Hended_eq; auto.
    exfalso. apply Hnot_seen.
    intros _.
    exists dep, cstate, inc.
    repeat split; try assumption.
    unfold FinSeen.
    apply Hended. reflexivity.
  Qed.

  (** The deployment conjunct is intentionally retained in the antecedent.
      Without it, [ltl_atom Count_Eq] is vacuously true before deployment and
      would incorrectly start a postcondition for an arbitrary [prev_count]. *)
  Lemma count_not_increase : forall caddr (str : ChainStream)
         (start : CStr_nth 0 str = empty_state)
         (prev_count : nat),
    satisfies contract caddr str 0
      (G ((l_dep l_and
            (l_atom (fun _ _ _ _
              (_ : DeploymentInfo Setup)
              (cstate : State)
              _ _
              (_ : list (ContractCallInfo Msg))
              _ =>
              cstate.(count) = prev_count)))
         l_impl
         (G (l_atom (fun _ _ _ _
              (_ : DeploymentInfo Setup)
              (cstate : State)
              _ _
              (_ : list (ContractCallInfo Msg))
              _ =>
              (cstate.(count) <= prev_count)%nat))))).
  Proof.
    intros caddr str start prev_count n _ Hpre.
    destruct Hpre as [Hdep_n Hcount_n].
    apply satisfies_ltl_dep_iff in Hdep_n.
    rename Hdep_n into deployed_n.
    cbn [satisfies] in Hcount_n.
    destruct_deployed_typed.
    rename dep_info0 into dep_info_n.
    rename cstate0 into cstate_n.
    rename inc_calls0 into inc_calls_n.
    rename Hdep_info into Hdep_info_n.
    rename Hcstate into Hcstate_n.
    rename Hinc_calls into Hinc_calls_n.
    rename H into Hcount_n_eq.

    solve_G.
    - auto.
    - (* Initial state of the suffix. *)
      cbn [satisfies].
      intros _.
      exists dep_info_n, cstate_n, inc_calls_n.
      repeat split; try assumption.
      rewrite Hcount_n_eq.
      apply Nat.le_refl.

    - (* Add block. *)
      intros j Hnj header queue_nil is_valid from_accs origin_acts env_eq
        dep_info_eq inc_calls_eq out_txs_eq IH tag.
      pose proof (CStr_wc_preserve str deployed_n j Hnj) as deployed_j.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rename H into Hle_prev.
      intros _.
      exists dep_info0, cstate0, inc_calls0.
      repeat split.
      + rewrite dep_info_eq. exact Hdep_info.
      + rewrite_environment_equiv.
        cbn [contract_state add_new_block_to_env].
        exact Hcstate.
      + rewrite inc_calls_eq. exact Hinc_calls.
      + exact Hle_prev.

    - (* A second deployment is impossible after [n]. *)
      intros j Hnj ctx setup state ctx_addr undeployed init_some env_eq
        dep_info_eq inc_calls_eq out_txs_eq inc_calls_nil out_txs_nil IH tag.
      pose proof (CStr_wc_preserve str deployed_n j Hnj) as deployed_j.
      congruence.

    - (* Outgoing action. *)
      intros j Hnj out_act tx tx_from_caddr tx_amount_eq tx_act_match
        chain_eq out_acts_eq dep_info_eq inc_calls_eq out_txs_eq
        deployed_prev state0 deployed_state_prev deployed_state_next IH tag.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rename H into Hle_prev.
      rewrite deployed_state_prev in Hcstate.
      injection Hcstate as Hcstate_eq.
      subst cstate0.
      intros _.
      exists dep_info0, state0, inc_calls0.
      repeat split.
      + rewrite dep_info_eq. exact Hdep_info.
      + exact deployed_state_next.
      + rewrite inc_calls_eq. exact Hinc_calls.
      + exact Hle_prev.

    - (* Nonrecursive call. *)
      intros j Hnj ctx prev_state msg prev_inc new_state new_acts
        ctx_addr from_other deployed_cstate receive_some env_eq dep_info_eq
        prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn in receive_some.
      pose proof (CStr_wc_preserve str deployed_n j Hnj) as deployed_j.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rename H into Hle_prev.
      rewrite deployed_cstate in Hcstate.
      injection Hcstate as Hcstate_eq.
      subst cstate0.
      assert (Hcall_count :
        (new_state.(count) <= prev_state.(count))%nat).
      { eapply contract_not_increase; eauto.
      }
      intros _.
      subst caddr.
      exists dep_info0, new_state,
        (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
          ctx.(ctx_amount) msg :: prev_inc).
      repeat split.
      + rewrite dep_info_eq. exact Hdep_info.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state].
        cbn.
        rewrite address_eq_refl, deserialize_serialize.
        reflexivity.
      + exact inc_calls_eq.
      + lia.

    - (* Recursive call. *)
      intros j Hnj ctx prev_state msg head prev_inc new_state new_acts
        ctx_addr from_self action_facts deployed_cstate receive_some env_eq
        dep_info_eq prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn in receive_some.
      pose proof (CStr_wc_preserve str deployed_n j Hnj) as deployed_j.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rename H into Hle_prev.
      rewrite deployed_cstate in Hcstate.
      injection Hcstate as Hcstate_eq.
      subst cstate0.
      assert (Hcall_count :
        (new_state.(count) <= prev_state.(count))%nat).
      { eapply contract_not_increase; eauto. }
      intros _.
      subst caddr.
      exists dep_info0, new_state,
        (build_call_info ctx.(ctx_limit) ctx.(ctx_origin) ctx.(ctx_from)
          ctx.(ctx_amount) msg :: prev_inc).
      repeat split.
      + rewrite dep_info_eq. exact Hdep_info.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state].
        cbn.
        rewrite address_eq_refl, deserialize_serialize.
        reflexivity.
      + exact inc_calls_eq.
      + lia.
  Qed.

End SafetyProperties.

Section LivenessProperties.

  (** Ranking function for the typed atom semantics. *)

  Definition count_rank
      (_ _ _ : nat)
      (_ : Address)
      (_ : DeploymentInfo Setup)
      (cstate : State)
      (_ : Amount)
      (_ : list ActionBody)
      (_ : list (ContractCallInfo Msg))
      (_ : list Tx) : option nat :=
    Some cstate.(count).

  Lemma fin_once caddr str (start : CStr_nth 0 str = empty_state) :
    let spec :=
      {|
        origin_addr_spec := fun addr => address_is_contract addr = false;
        amount_spec := fun amount => amount = 0%Z;
        msg_spec := fun msg => msg = Some Dec;
      |}
    in

    (forall min_limit, call_infinitely_often spec min_limit caddr str) ->
    satisfies contract caddr str 0
      (G
        ((l_dep l_and (l_not (l_atom FinSeen))) l_impl
        (F
          (G ((l_not (l_atom FinSeen)) l_impl
              (l_atom CanFin)))))).
  Proof.
    intros * Hfair *.
    intros n _ (Hdep_n & _).
    apply satisfies_ltl_dep_iff in Hdep_n.
    rename Hdep_n into deployed_n.
    cstr_destruct_deployed_typed.

    solve_U Nat.lt lt_wf Nat.lt_trans 0%nat Nat.eq_dec count_rank spec.

    - (* Initial typed rank. *)
      exists cstate.(count).
      split.
      + apply (proj1
          (deployed_iff_satisfies_ltl_dep contract caddr str n)).
        exact deployed_n.
      + cbn [satisfies count_rank].
        intros _.
        exists dep_info, cstate, inc_calls.
        repeat split; assumption.

    - (* [x = true] while the rank is non-bottom. *)
      cbn [satisfies]. auto.

    -
      exact Hfair.
    - exact deployed_n.
    - exact Hdep_info.
    - (* Rank exists at [n]. *)
      exists cstate.(count).
      cbn [satisfies count_rank].
      intros ?.
      exists dep_info, cstate, inc_calls.
      repeat split; assumption.

    -
      intros v1 chain dep cst out_acts inc txs ctx msg new_cst new_acts
        ctx_addr from_other receive_some prev_rank not_bot tag.
      pose proof (contract_not_increase chain ctx cst msg new_cst new_acts receive_some) as Hle.
      cbn [count_rank] in prev_rank. injection prev_rank as <-.
      cbn [rank_le count_rank]. unfold le_R. lia.

    -
      intros v1 chain dep cst head out_acts inc txs ctx msg new_cst new_acts
        ctx_addr from_self action_facts receive_some prev_rank not_bot tag.
      pose proof (contract_not_increase chain ctx cst msg new_cst new_acts receive_some) as Hle.
      cbn [count_rank] in prev_rank. injection prev_rank as <-.
      cbn [rank_le count_rank]. unfold le_R. lia.

    - (* A fair [Dec] strictly decreases every nonzero count. *)
      exists 1%nat.
      intros v1 j Hnj limit origin_addr amount msg acts
        prev_cstate prev_inc_calls deployed_prev deployed_cstate_prev
        Hinc_calls_j queue_prev enough_limit spec_origin_addr spec_amount
        spec_msg prev_rank not_bottom tag.
      pose proof (CStr_nth_reachable str start j) as reach_j.
      cbn in spec_origin_addr, spec_amount, spec_msg.
      subst msg.
      subst amount.

      let ctx := fresh "ctx" in
      pose (ctx := build_ctx limit origin_addr origin_addr caddr
        (if (origin_addr =? caddr)%address
         then env_account_balances (CStr_nth j str) caddr
         else (env_account_balances (CStr_nth j str) caddr + 0)%Z)
        0).

      cut (exists new_cstate new_acts,
        receive (CStr_nth j str) ctx prev_cstate (Some Dec) =
          Ok (new_cstate, new_acts)).
      + intros (new_cstate & new_acts & receive_some).
        let next := fresh "next" in
        cut (exists next : ChainState,
          inhabited (ActionEvaluation (CStr_nth j str)
            {|
              act_limit := limit;
              act_origin := origin_addr;
              act_from := origin_addr;
              act_body := act_call caddr 0 (serialize Dec)
            |}
            next
            (List.map (build_act (limit - 1) origin_addr caddr)
              new_acts)) /\
          chain_state_queue next =
            (List.map (build_act (limit - 1) origin_addr caddr)
              new_acts) ++ acts /\
          EnvironmentEquiv next
            (set_contract_state caddr (serialize new_cstate)
              (transfer_balance origin_addr caddr 0
                (CStr_nth j str)))).
        * let queue_next := fresh "queue_next" in
          let env_eq := fresh "env_eq" in
          intros (next & [eval] & queue_next & env_eq).
          contract_simpl; cbn in *.
          exists next.
          pose (ChainedList.snoc ChainedList.clnil
            (action_step (CStr_nth j str) next
              {|
                act_limit := limit;
                act_origin := origin_addr;
                act_from := origin_addr;
                act_body := act_call caddr 0 (serialize Dec)
              |}
              acts [] queue_prev eval queue_next)
            : ActionChainTrace (CStr_nth j str) next)
            as action_trace.
          exists action_trace.
          split; auto.
          intros finish_cstate finish_inc_calls Hcstate_next Hinc_calls_next.
          cbn in Hcstate_next.
          rewrite_environment_equiv in *.
          cbn in Hcstate_next.
          rewrite address_eq_refl, deserialize_serialize in Hcstate_next.
          inversion Hcstate_next; subst.
          cbn [count_rank] in prev_rank.
          inversion prev_rank; subst.
          cbn [rank_lt count_rank].
          cbn in *. lia.

        * apply (exist_step_call contract (CStr_nth j str)
             limit origin_addr origin_addr caddr 0 Dec
             acts new_acts prev_cstate new_cstate);
             auto; try lia.
          apply Z.ge_le.
          eapply account_balance_nonnegative; eauto.

      + (* [Dec] succeeds because a nonzero count cannot be ended. *)
        do 2 eexists.
        evaluate_receive.
        cbn [count_rank] in prev_rank.
        inversion prev_rank; subst v1.
        destruct (ended_correct_orig caddr (CStr_nth j str)
          reach_j deployed_prev)
          as (cstate_j & Hcstate_j & Hended_j).
        rewrite deployed_cstate_prev in Hcstate_j.
        inversion Hcstate_j; subst cstate_j.
        apply Hended_j.
        lia.

    - (* At rank zero, Fin remains enabled as long as it has not been used. *)
      cbn [satisfies].
      intros m Hnm Hrank_bot o Hmo Hnot_seen_o deployed_o.
      assert (deployed_m :
        env_contracts (CStr_nth m str) caddr =
          Some (contract : WeakContract)).
      { eapply (CStr_wc_preserve str deployed_n); eauto. }
      specialize (Hrank_bot deployed_m).
      destruct Hrank_bot as
        (dep_info_m & cstate_m & inc_calls_m &
         Hdep_info_m & Hcstate_m & Hinc_calls_m & Hrank_bot).
      cbn [count_rank] in Hrank_bot.
      injection Hrank_bot as Hcount_m.

      pose proof (count_not_increase caddr str start 0%nat)
        as Hcount_from_m.
      specialize (Hcount_from_m m ltac:(lia)).
      assert (Hpre_m :
        satisfies contract caddr str m
          (l_dep l_and
           (l_atom (fun _ _ _ _
             (_ : DeploymentInfo Setup)
             (cstate0 : State)
             _ _
             (_ : list (ContractCallInfo Msg))
             _ =>
             cstate0.(count) = 0%nat)))).
      {
        split.
        - apply (proj1
            (deployed_iff_satisfies_ltl_dep contract caddr str m)).
          exact deployed_m.
        - cbn [satisfies].
          intros _.
          exists dep_info_m, cstate_m, inc_calls_m.
          repeat split; try assumption.
      }
      specialize (Hcount_from_m Hpre_m).
      specialize (Hcount_from_m o Hmo).
      cbn [satisfies] in Hcount_from_m.
      specialize (Hcount_from_m deployed_o) as
        (dep_info_o & cstate_o & inc_calls_o &
         Hdep_info_o & Hcstate_o & Hinc_calls_o & Hcount_o).

      pose proof (end_not_seen_implies_not_ended caddr str start o ltac:(lia))
        as Hnot_ended.
      cbn [satisfies] in Hnot_ended.
      specialize (Hnot_ended Hnot_seen_o deployed_o) as
        (dep_info_o' & cstate_o' & inc_calls_o' &
         Hdep_info_o' & Hcstate_o' & Hinc_calls_o' & Hended_o).
      rewrite Hcstate_o in Hcstate_o'.
      injection Hcstate_o' as <-.

      exists dep_info_o, cstate_o, inc_calls_o.
      repeat split; try assumption.
      unfold CanFin.
      exists (build_ctx 0%nat caddr caddr caddr 0 0).
      exists (setter_from_getter_State_ended
        (fun _ : bool => true) cstate_o).
      evaluate_receive.
      all: try rewrite Hended_o; cbn; auto; try lia.
  Qed.

End LivenessProperties.
End CountDownOneTimeCorrect.
