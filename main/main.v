From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import LenguajeYul.dialect.
Require Import main.fran_dialect.
Require Import main.ast.
Require Import main.semantica.
Require Import main.parser.
Require Import main.equiv.

Module FranEVM_Dialect_ext <: PARSER_DIALECT.
    Include FranEVM_Dialect.
    Import EVM_opcode.
    
    Definition string_a_opcode (s : string) : option EVM_opcode.t :=
        (**string_dec sirve para comprobar igualdad de strings**)
        if string_dec s "add" then Some EVM_opcode.ADD 
        else if string_dec s "sub" then Some EVM_opcode.SUB
        else if string_dec s "mul" then Some EVM_opcode.MUL
        else if string_dec s "div" then Some EVM_opcode.DIV
        else if string_dec s "sdiv" then Some EVM_opcode.SDIV
        else if string_dec s "mod" then Some EVM_opcode.MOD
        else if string_dec s "smod" then Some EVM_opcode.SMOD
        else if string_dec s "exp" then Some EVM_opcode.EXP
        else if string_dec s "not" then Some EVM_opcode.NOT
        else if string_dec s "lt" then Some EVM_opcode.LT
        else if string_dec s "gt" then Some EVM_opcode.GT
        else if string_dec s "slt" then Some EVM_opcode.SLT
        else if string_dec s "sgt" then Some EVM_opcode.SGT
        else if string_dec s "eq" then Some EVM_opcode.EQ
        else if string_dec s "iszero" then Some EVM_opcode.ISZERO
        else if string_dec s "and" then Some EVM_opcode.AND
        else if string_dec s "or" then Some EVM_opcode.OR
        else if string_dec s "xor" then Some EVM_opcode.XOR
        else if string_dec s "byte" then Some EVM_opcode.BYTE
        else if string_dec s "shl" then Some EVM_opcode.SHL
        else if string_dec s "shr" then Some EVM_opcode.SHR
        else if string_dec s "sar" then Some EVM_opcode.SAR
        else if string_dec s "clz" then Some EVM_opcode.CLZ
        else if string_dec s "addmod" then Some EVM_opcode.ADDMOD
        else if string_dec s "mulmod" then Some EVM_opcode.MULMOD
        else if string_dec s "signextend" then Some EVM_opcode.SIGNEXTEND
        else None.

    Definition parsea_hex (s : string) : option U32.t :=
        match parsea_hex_aux s 0%Z with
        | Some z => Some (U32.to_t z) 
        | None => None
        end.

    Definition parsea_uint32 (s : string) : option U32.t :=
        match parsea_nat s with
        | Some n => Some (U32.to_t (Z.of_nat n))
        | None => None
        end.
    Definition parsea_ascii (s : string) : option U32.t :=
        match parsea_ascii_aux 100 s 0%Z with
        | Some z => Some (U32.to_t z)
        | None => None
        end.
    Definition parsea_literal (tok : string) : option U32.t :=
        if es_prefijo "0x" tok then
            parsea_hex (substring 2 (String.length tok - 2) tok)
        else if es_prefijo "hex""" tok then
            parsea_hex (substring 4 (String.length tok - 5) tok)
        else if es_prefijo """" tok then
            parsea_ascii (substring 1 (String.length tok - 2) tok)
        else
            parsea_uint32 tok.
            
End FranEVM_Dialect_ext.

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


		(*Ejemplos Hoare*)

    Require Import main.hoare.
    Module EVM_Hoare := YulHoare FranEVM_Dialect_ext FranAST.
    Import EVM_Hoare.
		Module Equiv := YulEquivalences FranEVM_Dialect_ext FranAST.
    Import FranAST.

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
			exists (fun e fe s => True).
			apply hoare_let with (R := fun res e fe s => 
                exists val, 
                res = (val)::nil /\ 
                Z.le 0 (U32.val val) /\ 
                Z.le (U32.val val) 5).
      - unfold hoare_triple.
				intros f env fenv state res env' fenv' state' Heval Hpre.
				destruct f; [discriminate|].
				inversion Heval; subst.
				exists (U32.to_t 3).
				split. reflexivity. unfold U32.val, U32.to_t. simpl.
        unfold U32.modulus. rewrite Z.mod_small. lia. split. lia. 
        vm_compute. reflexivity.
			- intros res env fenv state [val [Heq [H1 H2]]].
        subst.
				destruct (asignar_vars ("X" :: nil) (val::nil) env) eqn:H.
				exists val. unfold asignar_vars in H. 
				inversion H; subst.
				unfold EVM_Semantica.buscar_variable.
				destruct (string_dec "X" "X") as [Heq|Hneq].
				+ split. reflexivity. split. exact H1. exact H2.
				+ contradiction.
				+ discriminate H.
		Qed.

		Definition I : Assertion := fun e fe s =>
			exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val <= 3.

		Definition Q : Assertion := fun e fe s =>
			exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val = 3.

		Lemma eval_list_vacia :
    	forall (f:nat) env fenv state,
     		(f>0)%nat ->
      	Sem.eval_list f [] env fenv state = ([], env, fenv, state, Sem.Yul_Running).
    Proof.
      intros f env fenv state.
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
				let init := nil in
				let cond := YulOp EVM_opcode.LT (YulVar "X" :: YulConst (U32.to_t 3) :: nil) in
				let post := nil in
				let cuerpo := (YulLet ("X" :: nil) (YulOp EVM_opcode.ADD (YulVar "X" :: YulConst (U32.to_t 1) :: nil)))::nil in
				{{ P }} YulFor init cond post cuerpo {{ Q }}.
		Proof.
			exists I.
			pose (init := nil : list yul_expr).
			pose (cond := YulOp EVM_opcode.LT (YulVar "X" :: YulConst (U32.to_t 3) :: nil)).
			pose (post := nil : list yul_expr).
			pose (cuerpo := (YulLet ("X" :: nil) (YulOp EVM_opcode.ADD (YulVar "X" :: YulConst (U32.to_t 1) :: nil)))::nil).
			eapply hoare_for with (I := I) (init := init) (cond := cond) (post := post) (cuerpo := cuerpo).
			- apply hoare_empty_list.
			- intros f e fe s rc ec fec sc [val [Hb Hle]] Heval.
				destruct f as [|f0]; [discriminate|].
    		destruct f0 as [|f1]; [discriminate|].
    		destruct f1 as [|f2]; [discriminate|].
				simpl in Heval.
				unfold Sem.eval_yul in Heval.
				simpl in Heval.
				replace (Sem.buscar_variable "X" e) with (Some val) in Heval by exact (eq_sym Hb).
				simpl in Heval.
				inversion Heval;subst.
				exists val.
				split; auto.
				destruct f2 as [|f3]; [discriminate | simpl in Heval].
				rewrite Hb in Heval.
				destruct f3 as [|f4].
				simpl in Heval. 
				inversion Heval; subst. exact Hb.
				inversion Heval; subst. exact Hb.				
			- intros f e fe s rc ec fec sc [val [Hb HI]] Heval H.
				destruct f as [|f0]; [discriminate | simpl in Heval].
				destruct f0 as [|f1]; [discriminate | simpl in Heval].
				destruct f1 as [|f2]; [discriminate | simpl in Heval].
				destruct f2 as [|f3]; [discriminate | simpl in Heval].
				rewrite Hb in Heval.
				destruct f3 as [|f4]; [| simpl in Heval].
 				inversion Heval; subst.
				exists val.
				split.
				+ exact Hb.
				+ unfold Sem.is_true in H.
					unfold FranEVM_Dialect_ext.is_true_value in H.
  				unfold U32.lt in H.
					destruct (Z.ltb_spec (U32.val val) 3).
					* change (U32.val (U32.to_t 3)) with 3%Z in H.
						apply Z.ltb_lt in H0.
						rewrite H0 in H.
						vm_compute in H.
						discriminate H.
					* lia. 
				+ inversion Heval; subst.
					exists val. split. exact Hb. 
					unfold Sem.is_true in H.
					unfold FranEVM_Dialect_ext.is_true_value in H.
					unfold negb in H.
					destruct (U32.eqb (U32.lt val (U32.to_t 3)) U32.zero) eqn:Hif.
					* unfold U32.lt in Hif.
    				change (U32.val (U32.to_t 3)) with 3%Z in *.
						destruct (Z.ltb_spec (U32.val val) 3) as [Hlt | Hge].
						** 	vm_compute in Hif.
								discriminate Hif.
						** lia.
					* discriminate H.
			- intros f env_orig rc ec fec sc rb eb feb sb [val [Hb Hl]] H Hbreak.
				admit.
			- intros f env_orig rc ec fec sc rb eb feb sb rp ep fep sp ctrlb.
				intros H_I H_rc H_ctrlb H_cuerpo H_post.
				unfold post in H_post.
				rewrite eval_list_vacia in H_post.
				discriminate H_post.
				destruct f.
				simpl in H_post. discriminate H_post. lia. 
		
				




					






  			