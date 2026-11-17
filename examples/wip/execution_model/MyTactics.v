From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples.Wip.ExecutionModel Require Import Monad.
From ConCert.Examples.Wip.ExecutionModel Require Import ResultMonad.
From ConCert.Examples.Wip.ExecutionModel Require Import Serializable.
From ConCert.Examples.Wip.ExecutionModel Require Import ChainedList.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Streams.
From ConCert.Examples.Wip.ExecutionModel Require Import Blockchain.
From ConCert.Examples.Wip.ExecutionModel Require Import BlockchainBase.
From ConCert.Examples.Wip.ExecutionModel Require Import ContractCommon.

Ltac rewrite_queue :=
  repeat
    match goal with
    | [H: chain_state_queue _ = _ |- _] => rewrite H in *
    end.

Ltac inversion_some :=
  repeat match goal with
  | H : Some ?x = Some ?y |- _ =>
      let E := fresh "E" in
      inversion H as [E];
      clear H;
      try subst x;
      try subst y
  | H : (?x1, ?x2) = (?y1, ?y2) |- _ =>
      let E1 := fresh "E1" in
      let E2 := fresh "E2" in
      inversion H as [E1 E2];
      clear H;
      try subst x1; try subst x2;
      try subst y1; try subst y2
  end.

Ltac inversion_subst H :=
  injection H; clear H;
  repeat match goal with
  | |- ?x = ?y -> _ =>
      let E := fresh "E" in
      intro E; try subst x; try subst y; clear E
  end.

(* Ltac trace_induction :=
  match goal with
  | trace : ChainTrace ?from ?to |- _ =>
    remember from;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = from |- _ => subst x
    end;
    [ try (cbn; discriminate)
    | destruct_chain_step;
      specialize (IH ltac:(auto));
      try now rewrite_environment_equiv];
    auto
  end. *)

  Ltac action_trace_induction :=
    match goal with
    | trace : ActionChainTrace ?from ?to |- _ =>
      remember from;
      induction trace as [| * IH step];
      match goal with
      | H : ?x = from |- _ => subst x
      end;
      [ try (cbn; discriminate)
      | destruct_action_chain_step;
        specialize (IH ltac:(auto));
        try now rewrite_environment_equiv];
      auto
    end.

  Ltac action_trace_induction_intermidiate :=
    match goal with
    | H : ActionChainTrace ?mid ?to |- _ =>

        pattern to;
        match goal with
        | |- ?P to =>
            let A := fresh "A" in
            enough (forall st, ActionChainTrace mid st -> P st) as A;
            [
              cbn in *; eapply A; eauto
            |
            ];
            let action_trace := fresh "action_trace" in
            let IH := fresh "IH" in
            intros ?st action_trace;
            remember mid;
            induction action_trace as [| * IH ?step];
            match goal with
            | H : ?x = mid |- _ => subst x
            end;
            [
            | destruct_action_chain_step;
              specialize (IH ltac:(auto));
              try now rewrite_environment_equiv];
          auto
        end
    end.

(* Ltac destruct_trace_head :=
  match goal with
  | trace : ChainTrace ?from ?to |- _ =>
    destruct (trace_head_pattern_strong trace)
      as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
    ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
  | trace : ChainedList ChainState ChainStep ?from ?to |- _ =>
    destruct (trace_head_pattern_strong trace)
      as [length_zero |(?mid & ?step & ?trace' & ?trace_eq)]
    ;[destruct trace; cbn in length_zero; try lia; subst; clear length_zero|]
  end. *)

Ltac inversion_deployed_contract :=
  match goal with
  | [deployed: env_contracts ?env ?caddr = Some _,
      deployed' : env_contracts ?env ?caddr = Some ?wc' |- _] =>
      rewrite deployed in deployed'; inversion_subst deployed'
  | [deployed_state : contract_state ?env ?caddr = Some _,
      deployed_state' : contract_state ?env ?caddr = Some ?cstate' |- _] =>
      rewrite deployed_state in deployed_state'; inversion_subst deployed_state'
  | [deployed_state : env_contract_states ?env ?caddr = Some _,
      deployed_state' : match env_contract_states ?env ?caddr with
                  | Some val => deserialize val
                  | None => None
                  end = Some ?cstate' |- _
    ] =>
      rewrite deployed_state in deployed_state'; inversion_subst deployed_state'
  | [deployed_state : match env_contract_states ?env ?caddr with
                  | Some val => deserialize val
                  | None => None
                  end = Some _,
      deployed_state' : match env_contract_states ?env ?caddr with
                  | Some val => deserialize val
                  | None => None
                  end = Some ?cstate' |- _
    ] =>
      rewrite deployed_state in deployed_state'; inversion_subst deployed_state'
  end.

Local Ltac evaluate_receive_one_step :=
  lazymatch goal with
  | |- ?lhs = Ok ?rhs =>
      lazymatch lhs with
      | context[match ?g with | Ok _ => _ | Err _ => _ end] =>

          let A :=
            lazymatch type of g with
            | result ?A _ => A
            | ResultMonad.result ?A _ => A
            end
          in
          lazymatch g with
          | throwIf ?b ?e =>
              cut (b = false);
              [ let Hb := fresh "Hb" in
                intro Hb; rewrite Hb; cbn [throwIf] | ]
          | _ =>
            let x := fresh "x" in
            evar (x : A);
            cut (g = Ok x);
            let Hok := fresh "Hok" in
            intro Hok; rewrite Hok; cbn
          end
      end
  end.

Ltac evaluate_receive :=
  match goal with
  | |- BlockchainBase.receive ?contract ?chain ?ctx ?cstate ?msg = Ok (?new_cstate, ?new_acts) =>
      cbn; repeat evaluate_receive_one_step; auto
  | |- ?lhs = Ok (?new_cstate, ?new_acts) =>
      cbn; repeat evaluate_receive_one_step; auto
  end.

Ltac destruct_deployed_typed :=
  match goal with
  | deployed : env_contracts ?st ?caddr = Some ?contract,
    H : env_contracts ?st ?caddr = Some ?contract ->
        exists dep cstate inc,
          deployment_info _ _ _ = Some dep /\
          contract_state _ _ = Some cstate /\
          incoming_calls _ _ _ = Some inc /\ ?P |- _ =>
      let dep_info   := fresh "dep_info" in
      let cstate     := fresh "cstate" in
      let inc_calls  := fresh "inc_calls" in
      let Hdep_info  := fresh "Hdep_info" in
      let Hcstate    := fresh "Hcstate" in
      let Hinc_calls := fresh "Hinc_calls" in
      let HP         := fresh "H" in
      specialize (H deployed) as (dep_info & cstate & inc_calls & Hdep_info & Hcstate & Hinc_calls & HP)

  | deployed : env_contracts ?st ?caddr = Some ?contract,
    H : env_contracts ?st ?caddr = Some ?contract ->
        exists dep cstate inc,
          deployment_info _ _ _ = Some dep /\
          contract_state _ _ = Some cstate /\
          incoming_calls _ _ _ = Some inc |- _ =>
      let dep_info   := fresh "dep_info" in
      let cstate     := fresh "cstate" in
      let inc_calls  := fresh "inc_calls" in
      let Hdep_info  := fresh "Hdep_info" in
      let Hcstate    := fresh "Hcstate" in
      let Hinc_calls := fresh "Hinc_calls" in
      specialize (H deployed) as (dep_info & cstate & inc_calls & Hdep_info & Hcstate & Hinc_calls)
  end.

Ltac inv_ok_step :=
  match goal with
  | H : Err _ = Ok _ |- _ => discriminate H
  | H : Ok _ = Ok _ |- _ => injection H as H
  | H : (_, _) = (_, _) |- _ => injection H as H
  | H : ?x = ?y |- _ => is_var x; subst x
  | H : ?x = ?y |- _ => is_var y; subst y
  | H : match ?e with Ok _ => _ | Err _ => _ end = Ok _ |- _ =>
      let E := fresh "E" in destruct e eqn:E
  | H : match ?e with true => _ | false => _ end = Ok _ |- _ =>
      let E := fresh "E" in destruct e eqn:E
  | H : match ?e with (_, _) => _ end = Ok _ |- _ =>
      let E := fresh "E" in destruct e eqn:E
  end.

Ltac inv_ok_by simpl_tac :=
  repeat (simpl_tac; inv_ok_step).

Ltac addr_facts :=
  repeat match goal with
  | H : negb (address_eqb ?a ?b) = true |- _ =>
      destruct (address_eqb_spec a b); [discriminate H|]; clear H
  | H : negb (address_eqb ?a ?b) = false |- _ =>
      destruct (address_eqb_spec a b); [|discriminate H]; clear H
  | H : address_eqb ?a ?b = false |- _ =>
      destruct (address_eqb_spec a b); [discriminate H|]; clear H
  end.

Ltac bool_facts :=
  repeat match goal with
  | H : (_ <? _)%N = false |- _ => apply N.ltb_ge in H
  | H : (_ <? _)%N = true |- _ => apply N.ltb_lt in H
  | H : (_ <=? _)%N = false |- _ => apply N.leb_gt in H
  | H : (_ <=? _)%N = true |- _ => apply N.leb_le in H
  | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
  | H : (_ =? _)%N = false |- _ => apply N.eqb_neq in H
  | H : (_ >? _)%Z = false |- _ => rewrite Z.gtb_ltb in H; apply Z.ltb_ge in H
  | H : (_ >? _)%Z = true |- _ => rewrite Z.gtb_ltb in H; apply Z.ltb_lt in H
  end.
