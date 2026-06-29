From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import LenguajeYul.dialect.
Require Import main.fran_dialect.
Require Import main.fran_dialect_parser.
Require Import main.ast.
Require Import main.semantica.
Require Import main.parser.
Require Import main.equiv.

Module FranAST := YulAST FranEVM_Dialect_ext.
Module EVM_Parser := YulParser FranEVM_Dialect_ext FranAST.
Module EVM_Semantica := YulSemantica FranEVM_Dialect_ext FranAST.
    
Definition evaluar_evm (s : string) :=
  match EVM_Parser.parse_programa s with
  | Some ast => 
    EVM_Semantica.ejecutar_eval_bloque ast nil nil FranEVM_Dialect_ext.empty_dialect_state
  | None => 
    (nil, nil, nil, FranEVM_Dialect_ext.empty_dialect_state, Status.Error "Error de sintaxis")
  end.

	Compute evaluar_evm"{
        function power(base, exponent) -> result {
            switch exponent
            case 0 { result := 1 }
            case 1 { result := base }
            default {
                result := power(mul(base, base), div(exponent, 2))
                switch mod(exponent, 2)
                    case 1 { result := mul(base, result) }
            }
        }
        let x := power(3,2)
    }".

    Compute evaluar_evm"
    { 
    let zero := 0
    let v := 2
    {
        let y := add(sload(v), 1)
        v := y
    }  
    sstore(v, zero)
}".

	(*Ejemplos Hoare*)
  Require Import main.hoare.
  Module EVM_Hoare := YulHoare FranEVM_Dialect_ext FranAST.
  Import EVM_Hoare.
	Module Equiv := YulEquivalences FranEVM_Dialect_ext FranAST.
  Import FranAST.
  Import main.fran_dialect_parser.
	Include FranEVM_Dialect.

  Example equivalent_assertion1 : forall (v : U32.t),
    (fun e fe s => exists val, EVM_Semantica.buscar_variable "X" e = Some val /\ Z.le (U32.val val) 5) [ "X" |-> v ] 
    <<->> 
    (fun e fe s => Z.le (U32.val v) 5).
  Proof.
    split; unfold assert_implies, assertion_sub; intros env fenv state H; simpl in *.
		- destruct H as [val [Heq Hp]].
			inversion Heq; subst.
			exact Hp.
		- eauto.
	Qed.

	Example equivalent_assertion2 : forall (v : U32.t),
    (fun e fe s => exists val, EVM_Semantica.buscar_variable "X" e = Some val /\ Z.le (U32.val val) 5) [ "X" |-> U32.add v U32.one ] 
    <<->> 
    (fun e fe s => Z.le (U32.val (U32.add v U32.one)) 5).
  Proof.
		split; unfold assert_implies, assertion_sub; intros env fenv state H; simpl in *.
		- destruct H as [val [Hneq Hp]].
			inversion Hneq; subst.
			exact Hp.
		- eauto.
	Qed.

	Example hoare_asgn_examples2 :
		exists P,
			{{ P }}
				YulLet ("X" :: nil) (YulConst (U32.to_t 3))
			{{ fun e fe s => exists val, EVM_Semantica.buscar_variable "X" e = Some val /\ Z.le 0 (U32.val val) /\ Z.le (U32.val val) 5 }}.
	Proof.
		exists (fun e fe s => existsb (fun '(m, _) => String.eqb "X" m) e = false).
			apply hoare_let with (R := fun res e fe s => 
                exists val, 
                res = (val)::nil /\ 
                Z.le 0 (U32.val val) /\ 
                Z.le (U32.val val) 5 /\
                existsb (fun '(m, _) => String.eqb "X" m) e = false).
      - unfold hoare_triple, hoare_triple_val.
				intros f env fenv state res env' fenv' state' Heval Hpre.
				destruct f; [discriminate|].
				inversion Heval; subst.
				exists (U32.to_t 3).
				split. reflexivity. unfold U32.val, U32.to_t. simpl.
        unfold U32.modulus. rewrite Z.mod_small; [|lia]. split; [lia|].
        split; [lia|]. exact Hpre.
			- intros res env fenv state [val [Heq [H1 [H2 Hex]]]].
        subst.
				destruct (Sem.agregar_vars ("X" :: nil) (val::nil) env) eqn:H.
				* exists val. unfold Sem.agregar_vars in H.
				  rewrite Hex in H.
				  cbn in H. inversion H; subst.
				  unfold EVM_Semantica.buscar_variable.
				  destruct (string_dec "X" "X") as [HeqX|HneqX].
				  + split. reflexivity. split. exact H1. exact H2.
				  + contradiction.
				* unfold Sem.agregar_vars in H.
				  rewrite Hex in H.
				  cbn in H. discriminate H.
		Qed.

		Definition I : Assertion := fun e fe s =>
			exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val <= 3.

		Definition Q : Assertion := fun e fe s =>
			exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val = 3.

		Lemma eval_list_vacia :
    	forall (f:nat) env fenv state en_bucle,
     		(f>0)%nat ->
      	Sem.eval_list f [] env fenv state en_bucle = ([], env, fenv, state, Sem.Yul_Running).
    Proof.
      intros f env fenv state en_bucle.
      destruct f; unfold Sem.eval_list. lia. reflexivity.
    Qed.

		Lemma existsb_env_in : forall (env : yul_env) (n : string) (v : FranEVM_Dialect_ext.value_t), In (n, v) env -> existsb (fun '(m, _) => String.eqb n m) env = true.
    Proof.
      induction env as [| [n' v'] resto IH]; intros n v Hin.
      - contradiction.
      - simpl. destruct Hin as [Heq | Hin].
        + inversion Heq; subst. rewrite String.eqb_refl. reflexivity.
        + apply IH in Hin.
          destruct (String.eqb n n').
          * reflexivity.
          * exact Hin.
    Qed.

		Lemma filter_env_id : forall (env1 env2 : yul_env), (forall n v, In (n, v) env1 -> existsb (fun '(m, _) => String.eqb n m) env2 = true) ->
        filter (fun '(n, _) => existsb (fun '(m, _) => String.eqb n m) env2) env1 = env1.
    Proof.
      induction env1 as [| [k v'] resto IH]; intros env2 H.
      - reflexivity.
      - simpl.
          assert (H_h : existsb (fun '(m, _) => String.eqb k m) env2 = true).
          { apply (H k v'). left. reflexivity. }
          rewrite H_h. 
          f_equal.
          apply IH.
          intros n' v'' Hin.             
          apply (H n' v''). right. exact Hin.
    Qed.

    Lemma restringe_env_mismo : forall (env : yul_env), Sem.restringe_env env env = env.
    Proof.
      intros env.
      unfold Sem.restringe_env.
      apply filter_env_id.
      intros n v Hin.
      apply (existsb_env_in env n v).
      exact Hin.
    Qed.
		

		Example for_example :
			exists P,
				let cond := YulOp EVM_opcode.LT (YulVar "X" :: YulConst (U32.to_t 3) :: nil) in
				let cuerpo := (YulAsignar ("X"::nil) (YulOp EVM_opcode.ADD (YulVar "X" :: YulConst (U32.to_t 1) :: nil)))::nil in
				hoare_triple P
					(YulFor nil cond nil cuerpo)
				  (fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val = 3).
		Proof.
			exists (fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val <= 3).
			eapply hoare_for with (I := fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val <= 3).
			(* 1. init (vacío) preserva el invariante *)
			- intros f e fe s res e' fe' s' Heval [val [Hb Hl]].
				peel_fuel_in Heval. inversion Heval; subst.
				exists val. split; auto.
			(* 2. evaluar la condición preserva el invariante *)
			- intros f e fe s rc ec fec sc [val [Hb Hl]] Heval.
				eval_expr_in Heval Hb. inversion Heval; subst.
				exists val. split; auto.
			(* 3. condición falsa → postcondición *)
			- intros f e fe s rc ec fec sc [val [Hb Hl]] Heval Hfalse.
				eval_expr_in Heval Hb. inversion Heval; subst.
				exists val. split; [exact Hb|].
				unfold is_true, FranEVM_Dialect_ext.is_true_value, U32.eqb, U32.lt, U32.to_t, U32.zero in Hfalse.
				cbn in Hfalse.
				destruct (Z.ltb (U32.val val) 3) eqn:Hlt.
				+ cbn in Hfalse. discriminate Hfalse.
				+ apply Z.ltb_ge in Hlt. lia.
			(* 4. break en cuerpo (imposible: cuerpo no tiene break) *)
			- intros f env_orig rc ec fec sc rb eb feb sb [val [Hb Hl]] Htrue Hbody.
				eval_expr_in Hbody Hb. inversion Hbody.
			(* 5. break en post (imposible: post es vacío) *)
			- intros f env_orig rc ec fec sc rb eb feb sb rp ep fep sp ctrlb.
				intros [val [Hb Hl]] Htrue Hctrlb Hbody Hpost.
				peel_fuel_in Hpost. inversion Hpost; discriminate.
			(* 6. paso del bucle → invariante se mantiene *)
			- intros f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp.
				intros [val [Hb Hle]] Hcond Htrue Hctrlb Hbody Hpost Hctrlp.
				Opaque Sem.restringe_env.
				eval_expr_in Hcond Hb. inversion Hcond; subst.
				repeat (destruct f as [|f]; [inversion Hbody; subst; destruct Hctrlb; discriminate | cbn in Hbody]).
				rewrite Hb in Hbody. cbn in Hbody.
				rewrite Hb in Hbody. cbn in Hbody.
				inversion Hbody; subst.
				inversion Hpost; subst.
				exists (U32.add val (U32.to_t 1)). split.
				+ apply buscar_restringe.
				  * apply buscar_restringe.
				    -- solve_buscar.
				    -- intro H; rewrite H in Hb; discriminate Hb.
				  * match goal with
				    | |- Sem.buscar_variable "X" ?env <> None =>
				        assert (H_not_none: Sem.buscar_variable "X" env = Some (U32.add val (U32.to_t 1)))
				    end.
				    { apply buscar_restringe; [solve_buscar | intro H; rewrite H in Hb; discriminate Hb]. }
				    intro H_absurd; rewrite H_not_none in H_absurd; discriminate H_absurd.
				+ unfold Sem.is_true, U32.lt, U32.to_t in Htrue; cbn in Htrue.
				  destruct (U32.val val <? 3)%Z eqn:Hltb; [|discriminate Htrue].
				  apply Z.ltb_lt in Hltb. unfold U32.add; cbn.
				  pose proof (U32.is_valid val) as Hbounds.
				  unfold U32.Valid in Hbounds.
				  rewrite Z.mod_small; lia.
				Transparent Sem.restringe_env.
		Qed.

