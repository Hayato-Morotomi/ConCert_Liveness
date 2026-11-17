From Stdlib Require Import ZArith NArith String List Lia Bool. Import ListNotations.
From ConCert.Utils Require Import RecordUpdate Extras.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain ResultMonad Serializable Monad ContractCommon Containers.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedStream ChainStream.
From ConCert.Examples.Wip.LTL Require Import MyLTLBase. Import LTLNotation.
From ConCert.Examples.Wip.ExecutionModel Require Import MyTactics ChainedList ChainStepDetermin MyBuildUtils.
From ConCert.Examples.Wip.LTL Require Import MyLTL_G.

Section LTLUtils.
  Context {BaseTypes : ChainBase}.
  Context {Setup Msg State Error : Type}
          `{ser_setup : Serializable Setup}
          `{ser_msg : Serializable Msg}
          `{ser_state : Serializable State}
          `{ser_error : Serializable Error}.

  Context {contract : Contract Setup Msg State Error}.

  Lemma G_state_pred (Q : Address -> State -> Prop) caddr str (start : CStr_nth 0 str = empty_state) j :
    (forall chain ctx cs msg new_cs acts,
        receive contract chain ctx cs msg = Ok (new_cs, acts) -> Q caddr cs -> Q caddr new_cs) ->
    satisfies contract caddr str j (l_dep l_and (l_atom (fun _ _ _ a _ cs _ _ _ _ => Q a cs))) ->
    satisfies contract caddr str j (G (l_atom (fun _ _ _ a _ cs _ _ _ _ => Q a cs))).
  Proof.
    intros Hrecv [Hdep_j HQ_j].
    apply satisfies_ltl_dep_iff in Hdep_j. rename Hdep_j into deployed_n.
    solve_G; auto.
    - (* AddBlock *)
      intros k Hjk header queue_nil is_valid from_accs origin_acts env_eq
        dep_info_eq inc_calls_eq out_txs_eq IH tag.
      pose proof (CStr_wc_preserve str deployed_n k Hjk) as deployed_k.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      intros _. eexists _, _, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv. cbn [contract_state add_new_block_to_env]. eassumption.
      + rewrite inc_calls_eq. eassumption.
      + eassumption.
    -
      intros k Hjk ctx setup state ctx_addr undeployed. intros.
      pose proof (CStr_wc_preserve str deployed_n k Hjk). congruence.
    - (* Outgoing *)
      intros k Hjk out_act tx tx_from_caddr tx_amount_eq tx_act_match
        chain_eq out_acts_eq dep_info_eq inc_calls_eq out_txs_eq
        deployed_prev state0 deployed_state_prev deployed_state_next IH tag.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rewrite deployed_state_prev in Hcstate. injection Hcstate as <-.
      intros _. eexists _, _, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + exact deployed_state_next.
      + rewrite inc_calls_eq. eassumption.
      + eassumption.
    - (* Nonrecursive call *)
      intros k Hjk ctx prev_state msg prev_inc new_state new_acts
        ctx_addr from_other deployed_cstate receive_some env_eq dep_info_eq
        prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      pose proof (CStr_wc_preserve str deployed_n k Hjk) as deployed_k.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rewrite deployed_cstate in Hcstate. injection Hcstate as <-.
      intros _. subst caddr.
      eexists _, new_state, _.
      repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|eassumption].
    - (* Recursive call *)
      intros k Hjk ctx prev_state msg head prev_inc new_state new_acts
        ctx_addr from_self action_facts deployed_cstate receive_some env_eq
        dep_info_eq prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      pose proof (CStr_wc_preserve str deployed_n k Hjk) as deployed_k.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rewrite deployed_cstate in Hcstate. injection Hcstate as <-.
      intros _. subst caddr.
      eexists _, new_state, _.
      repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|eassumption].
  Qed.

  Lemma G_state_pred_init (Q : Address -> State -> Prop) caddr str (start : CStr_nth 0 str = empty_state) :
    (forall chain ctx setup st,
        ctx_contract_address ctx = caddr -> init contract chain ctx setup = Ok st -> Q caddr st) ->
    (forall chain ctx cs msg new_cs acts,
        receive contract chain ctx cs msg = Ok (new_cs, acts) -> Q caddr cs -> Q caddr new_cs) ->
    satisfies contract caddr str 0 (G (l_atom (fun _ _ _ a _ cs _ _ _ _ => Q a cs))).
  Proof.
    intros Hinit Hrecv.
    solve_G; auto.
    -
      cbn [satisfies]. intros Hd. rewrite start in Hd. discriminate.
    - (* AddBlock *)
      intros k Hjk header queue_nil is_valid from_accs origin_acts env_eq
        dep_info_eq inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      exists d, c, i. repeat split; auto.
      + rewrite dep_info_eq. exact H1.
      + rewrite_environment_equiv. cbn [contract_state add_new_block_to_env]. exact H2.
      + rewrite inc_calls_eq. exact H3.
    - (* Deploy *)
      intros k Hjk ctx setup state ctx_addr undeployed init_some env_eq
        dep_info_eq inc_calls_eq out_txs_eq inc_calls_nil out_txs_nil IH tag.
      cbn [satisfies]. intros _.
      exists (build_deployment_info ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) setup), state, [].
      repeat split.
      + exact dep_info_eq.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state add_contract]. cbn.
        subst caddr. rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + rewrite inc_calls_eq. exact inc_calls_nil.
      + eapply Hinit; [exact ctx_addr|exact init_some].
    - (* Outgoing *)
      intros k Hjk out_act tx tx_from_caddr tx_amount_eq tx_act_match
        chain_eq out_acts_eq dep_info_eq inc_calls_eq out_txs_eq
        deployed_prev state0 deployed_state_prev deployed_state_next IH tag.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rewrite deployed_state_prev in Hcstate. injection Hcstate as <-.
      intros _. eexists _, _, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + exact deployed_state_next.
      + rewrite inc_calls_eq. eassumption.
      + eassumption.
    - (* Nonrecursive call *)
      intros k Hjk ctx prev_state msg prev_inc new_state new_acts
        ctx_addr from_other deployed_cstate receive_some env_eq dep_info_eq
        prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      rewrite deployed_cstate in H2. injection H2 as <-.
      subst caddr. eexists _, new_state, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|eassumption].
    - (* Recursive call *)
      intros k Hjk ctx prev_state msg head prev_inc new_state new_acts
        ctx_addr from_self action_facts deployed_cstate receive_some env_eq
        dep_info_eq prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      rewrite deployed_cstate in H2. injection H2 as <-.
      subst caddr. eexists _, new_state, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|eassumption].
  Qed.

  Lemma G_state_inc_pred_init (Q : State -> list (ContractCallInfo Msg) -> Prop) caddr str (start : CStr_nth 0 str = empty_state) :
    (forall chain ctx setup st, init contract chain ctx setup = Ok st -> Q st []) ->
    (forall chain ctx cs msg new_cs acts x l,
        receive contract chain ctx cs msg = Ok (new_cs, acts) -> call_msg x = msg -> Q cs l -> Q new_cs (x :: l)) ->
    satisfies contract caddr str 0 (G (l_atom (fun _ _ _ _ _ cs _ _ inc _ => Q cs inc))).
  Proof.
    intros Hinit Hrecv.
    solve_G; auto.
    -
      cbn [satisfies]. intros Hd. rewrite start in Hd. discriminate.
    - (* AddBlock *)
      intros k Hjk header queue_nil is_valid from_accs origin_acts env_eq
        dep_info_eq inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      exists d, c, i. repeat split; auto.
      + rewrite dep_info_eq. exact H1.
      + rewrite_environment_equiv. cbn [contract_state add_new_block_to_env]. exact H2.
      + rewrite inc_calls_eq. exact H3.
    - (* Deploy *)
      intros k Hjk ctx setup state ctx_addr undeployed init_some env_eq
        dep_info_eq inc_calls_eq out_txs_eq inc_calls_nil out_txs_nil IH tag.
      cbn [satisfies]. intros _.
      exists (build_deployment_info ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount) setup), state, [].
      repeat split.
      + exact dep_info_eq.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state add_contract]. cbn.
        subst caddr. rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + rewrite inc_calls_eq. exact inc_calls_nil.
      + eapply Hinit; exact init_some.
    - (* Outgoing *)
      intros k Hjk out_act tx tx_from_caddr tx_amount_eq tx_act_match
        chain_eq out_acts_eq dep_info_eq inc_calls_eq out_txs_eq
        deployed_prev state0 deployed_state_prev deployed_state_next IH tag.
      cbn [satisfies] in IH |- *.
      destruct_deployed_typed.
      rewrite deployed_state_prev in Hcstate. injection Hcstate as <-.
      intros _. eexists _, _, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + exact deployed_state_next.
      + rewrite inc_calls_eq. eassumption.
      + eassumption.
    - (* Nonrecursive call *)
      intros k Hjk ctx prev_state msg prev_inc new_state new_acts
        ctx_addr from_other deployed_cstate receive_some env_eq dep_info_eq
        prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      rewrite deployed_cstate in H2. injection H2 as <-.
      rewrite prev_inc_calls_some in H3. injection H3 as <-.
      subst caddr. eexists _, new_state, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|reflexivity|eassumption].
    - (* Recursive call *)
      intros k Hjk ctx prev_state msg head prev_inc new_state new_acts
        ctx_addr from_self action_facts deployed_cstate receive_some env_eq
        dep_info_eq prev_inc_calls_some inc_calls_eq out_txs_eq IH tag.
      cbn [satisfies] in IH |- *. intros deployed_Sk.
      assert (deployed_k : env_contracts (CStr_nth k str) caddr = Some (contract : WeakContract)).
      { rewrite_environment_equiv in deployed_Sk. exact deployed_Sk. }
      destruct (IH deployed_k) as (d & c & i & H1 & H2 & H3 & HQ).
      rewrite deployed_cstate in H2. injection H2 as <-.
      rewrite prev_inc_calls_some in H3. injection H3 as <-.
      subst caddr. eexists _, new_state, _. repeat split.
      + rewrite dep_info_eq. eassumption.
      + rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        rewrite address_eq_refl, deserialize_serialize. reflexivity.
      + exact inc_calls_eq.
      + eapply Hrecv; [exact receive_some|reflexivity|eassumption].
  Qed.

  Lemma cstr_slot_mono (str : ChainStream) (start : CStr_nth 0 str = empty_state) i j :
    (i <= j)%nat -> (current_slot (CStr_nth i str) <= current_slot (CStr_nth j str))%nat.
  Proof.
    intros Hij.
    apply reachable_through_current_slot.
    split; [apply CStr_nth_reachable; auto|].
    constructor. exact (CStr_clist_n_m str i j Hij).
  Qed.

  Lemma cstr_queue_empties (str : ChainStream) (start : CStr_nth 0 str = empty_state) :
    forall l i, (CStr_nth i str).(chain_state_queue) = l ->
    exists j, (i <= j)%nat /\ (CStr_nth j str).(chain_state_queue) = [].
  Proof.
    induction l as [|act acts IH]; intros i Hq.
    - exists i. split; auto.
    - destruct (cstr_act_terminate str start i act acts Hq) as (j & Hij & Hqj).
      destruct (IH j Hqj) as (k & Hjk & Hqk).
      exists k. split; [lia|exact Hqk].
  Qed.

  Lemma cstr_block_after_empty (str : ChainStream) i :
    (CStr_nth i str).(chain_state_queue) = [] ->
    (current_slot (CStr_nth i str) < current_slot (CStr_nth (S i) str))%nat.
  Proof.
    intros Hq.
    pose proof (CStr_link str i) as step.
    destruct_chain_step; try congruence.
    rewrite_environment_equiv. cbn.
    inversion valid_header. lia.
  Qed.

  Lemma time_diverges (str : ChainStream) (start : CStr_nth 0 str = empty_state) :
    forall n, exists j, (n <= current_slot (CStr_nth j str))%nat.
  Proof.
    induction n as [|n IH].
    - exists 0%nat. lia.
    - destruct IH as (j & Hj).
      destruct (cstr_queue_empties str start _ j eq_refl) as (k & Hjk & Hqk).
      pose proof (cstr_slot_mono str start j k Hjk).
      pose proof (cstr_block_after_empty str k Hqk).
      exists (S k). lia.
  Qed.

  Lemma inc_calls_step caddr str (start : CStr_nth 0 str = empty_state) q :
    env_contracts (CStr_nth (S q) str) caddr = Some (contract : WeakContract) ->
    incoming_calls Msg (CStr_clist str (S q)) caddr = incoming_calls Msg (CStr_clist str q) caddr
    \/ exists x r, incoming_calls Msg (CStr_clist str q) caddr = Some r
              /\ incoming_calls Msg (CStr_clist str (S q)) caddr = Some (x :: r).
  Proof.
    intros Hd.
    pose proof (contract_addr_format caddr contract (CStr_nth_reachable str start (S q)) Hd) as Haddr.
    destruct (contract_step_case_complete_focused contract caddr str start Haddr q Hd) as [cstep].
    destruct cstep; try (left; exact inc_calls_eq).
    - right. do 2 eexists. split; [exact prev_inc_calls_some|exact inc_calls_eq].
    - right. do 2 eexists. split; [exact prev_inc_calls_some|exact inc_calls_eq].
    - left. destruct c as [_ Hview]. destruct (Hview Hd) as (_ & _ & Hinc_eq & _). congruence.
  Qed.

  Lemma inc_calls_new caddr str (start : CStr_nth 0 str = empty_state) i li :
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract) ->
    incoming_calls Msg (CStr_clist str i) caddr = Some li ->
    forall p lp, (i <= p)%nat ->
      incoming_calls Msg (CStr_clist str p) caddr = Some lp ->
      exists new, lp = new ++ li
        /\ forall x, List.In x new ->
             exists j r, (i <= j < p)%nat
               /\ incoming_calls Msg (CStr_clist str j) caddr = Some r
               /\ incoming_calls Msg (CStr_clist str (S j)) caddr = Some (x :: r).
  Proof.
    intros Hd Hli p. induction p as [|q IH]; intros lp Hip Hlp.
    - assert (i = 0)%nat by lia. subst i. rewrite Hli in Hlp. injection Hlp as <-.
      exists []. split; [reflexivity|]. intros x [].
    - destruct (Nat.eq_dec i (S q)) as [Hi|Hne].
      { subst i. rewrite Hli in Hlp. injection Hlp as <-. exists []. split; [reflexivity|]. intros x []. }
      assert (Hiq : (i <= q)%nat) by lia.
      assert (Hd' : env_contracts (CStr_nth (S q) str) caddr = Some (contract : WeakContract))
        by (apply (CStr_wc_preserve str Hd); lia).
      destruct (inc_calls_step caddr str start q Hd') as [Heq|(y & r & Hr & Hyr)].
      + rewrite Heq in Hlp. destruct (IH lp Hiq Hlp) as (new & -> & Hnew).
        exists new. split; [reflexivity|]. intros x Hx.
        destruct (Hnew x Hx) as (j & r & Hj & H1 & H2). exists j, r. split; [lia|auto].
      + rewrite Hyr in Hlp. injection Hlp as <-.
        destruct (IH r Hiq Hr) as (new & -> & Hnew).
        exists (y :: new). split; [reflexivity|]. intros x [<-|Hx].
        * exists q, (new ++ li). split; [lia|]. split; [exact Hr|exact Hyr].
        * destruct (Hnew x Hx) as (j & r' & Hj & H1 & H2). exists j, r'. split; [lia|auto].
  Qed.

  Lemma cstr_step_cases caddr (str : ChainStream) (start : CStr_nth 0 str = empty_state) q :
    env_contracts (CStr_nth q str) caddr = Some (contract : WeakContract) ->
    (contract_state (CStr_nth (S q) str) caddr = contract_state (CStr_nth q str) caddr :> option State
     /\ incoming_calls Msg (CStr_clist str (S q)) caddr = incoming_calls Msg (CStr_clist str q) caddr)
    \/ (exists (chain : Chain) ctx cs msg cs' acts lq x,
          contract_state (CStr_nth q str) caddr = Some cs
          /\ contract_state (CStr_nth (S q) str) caddr = Some cs'
          /\ incoming_calls Msg (CStr_clist str q) caddr = Some lq
          /\ incoming_calls Msg (CStr_clist str (S q)) caddr = Some (x :: lq)
          /\ call_msg x = msg
          /\ current_slot chain = current_slot (CStr_nth q str)
          /\ receive contract chain ctx cs msg = Ok (cs', acts)).
  Proof.
    intros Hd.
    assert (Hd' : env_contracts (CStr_nth (S q) str) caddr = Some (contract : WeakContract))
      by (apply (CStr_wc_preserve str Hd); lia).
    pose proof (contract_addr_format caddr contract (CStr_nth_reachable str start (S q)) Hd') as Haddr.
    destruct (contract_step_case_complete_focused contract caddr str start Haddr q Hd') as [cstep].
    destruct cstep.
    - left. split; [|exact inc_calls_eq].
      rewrite_environment_equiv; cbn [contract_state add_new_block_to_env]; reflexivity.
    - congruence.
    - left. split; [congruence|exact inc_calls_eq].
    - right. do 8 eexists. split; [exact deployed_cstate|]. split.
      { rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        subst caddr. rewrite address_eq_refl, deserialize_serialize. reflexivity. }
      split; [exact prev_inc_calls_some|]. split; [exact inc_calls_eq|].
      split; [reflexivity|]. split; [reflexivity|exact receive_some].
    - right. do 8 eexists. split; [exact deployed_cstate|]. split.
      { rewrite_environment_equiv.
        cbn [contract_state set_contract_state set_chain_contract_state]. cbn.
        subst caddr. rewrite address_eq_refl, deserialize_serialize. reflexivity. }
      split; [exact prev_inc_calls_some|]. split; [exact inc_calls_eq|].
      split; [reflexivity|]. split; [reflexivity|exact receive_some].
    - left. destruct c as [_ Hview]. destruct (Hview Hd') as (_ & Hcs_eq & Hinc_eq & _).
      split; congruence.
  Qed.

  Lemma state_pred_kept (Q : State -> Prop) caddr (str : ChainStream) (start : CStr_nth 0 str = empty_state) i :
    env_contracts (CStr_nth i str) caddr = Some (contract : WeakContract) ->
    (forall chain ctx cs msg cs' acts, receive contract chain ctx cs msg = Ok (cs', acts) -> Q cs -> Q cs') ->
    (forall cs, contract_state (CStr_nth i str) caddr = Some cs -> Q cs) ->
    forall k, (i <= k)%nat -> forall cs, contract_state (CStr_nth k str) caddr = Some cs -> Q cs.
  Proof.
    intros Hd Hpres Hi k. induction k as [|q IH]; intros Hik cs Hcs.
    - assert (i = 0)%nat by lia. subst i. exact (Hi cs Hcs).
    - destruct (Nat.eq_dec i (S q)) as [Heq|Hne]; [subst i; exact (Hi cs Hcs)|].
      assert (Hdq : env_contracts (CStr_nth q str) caddr = Some (contract : WeakContract))
        by (apply (CStr_wc_preserve str Hd); lia).
      destruct (cstr_step_cases caddr str start q Hdq)
        as [[Hcs_eq _]|(chain & ctx & csq & msg & cs' & acts & lq & x & Hcsq & Hcs' & _ & _ & _ & _ & Hr)].
      + rewrite Hcs_eq in Hcs. exact (IH ltac:(lia) cs Hcs).
      + rewrite Hcs' in Hcs. injection Hcs as <-. exact (Hpres _ _ _ _ _ _ Hr (IH ltac:(lia) csq Hcsq)).
  Qed.
End LTLUtils.
