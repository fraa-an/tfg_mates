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
Require Import main.hoare.


(*Módulos concretos de semántica y parser*)
Module FranAST := YulAST FranEVM_Dialect_ext.
Module Hoare := YulHoare FranEVM_Dialect_ext FranAST.
Module Sem := Hoare.Sem.
Module Par := YulParser FranEVM_Dialect_ext FranAST.
Module Equiv := YulEquivalences FranEVM_Dialect_ext FranAST.
Import Hoare.
Import FranAST.

(*Función auxiliar: parsea y ejecuta código Yul dado como string*)
Definition evaluar_evm (code : string) :=
  match Par.parse_programa code with
  | None => ([], [], [], FranEVM_Dialect_ext.empty_dialect_state, Status.Error "parse error")
  | Some ast =>
      Sem.ejecutar_eval_bloque ast [] [] FranEVM_Dialect_ext.empty_dialect_state
  end.

(*
  Ejemplo 1: almacena el valor 1 en la posición 0 de storage.
  { let v := 1  let zero := 0  sstore(zero, v) }
*)
Compute evaluar_evm "{ let v := 1 let zero := 0 sstore(zero, v) }".

(*
  Ejemplo 2: función power que calcula x^n iterativamente.
  { function power(base, n) -> result { result := 1  for {} gt(n, 0) {} { result := mul(result, base) n := sub(n, 1) } } let r := power(2, 3) }
*)
Compute evaluar_evm "{ function power(base, n) -> result { result := 1 for {} gt(n, 0) {} { result := mul(result, base) n := sub(n, 1) } } let r := power(2, 3) }".


Example equivalent_assertion1 : forall (v : U32.t),
  (fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ Z.le (U32.val val) 5) [ "X" |-> v ] 
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
  (fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ Z.le (U32.val val) 5) [ "X" |-> U32.add v U32.one ] 
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
		{{ fun e fe s => exists val, Sem.buscar_variable "X" e = Some val /\ Z.le 0 (U32.val val) /\ Z.le (U32.val val) 5 }}.
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
		* exists val. split; [|split; assumption].
            cbn in H. 
            assert (H_none: Sem.buscar_variable "X" env = None).
            { clear - Hex. induction env as [| [m v] env' IH].
              - reflexivity.
              - change (existsb (fun '(m0, _) => String.eqb "X" m0) ((m, v) :: env')) with (String.eqb "X" m || existsb (fun '(m0, _) => String.eqb "X" m0) env') in Hex.
                apply Bool.orb_false_iff in Hex. destruct Hex as [H_eq Hex'].
                cbn [Sem.buscar_variable]. destruct (string_dec "X" m) as [e | e].
                + apply String.eqb_eq in e. rewrite e in H_eq. discriminate H_eq.
                + apply IH. exact Hex'.
            }
            rewrite H_none in H.
            cbn in H.
            inversion H; subst.
            cbn [Sem.buscar_variable]. destruct (string_dec "X" "X"); [reflexivity|contradiction].
		* cbn in H.
      assert (H_none: Sem.buscar_variable "X" env = None).
      { clear - Hex. induction env as [| [m v] env' IH].
      - reflexivity.
      - change (existsb (fun '(m0, _) => String.eqb "X" m0) ((m, v) :: env')) with (String.eqb "X" m || existsb (fun '(m0, _) => String.eqb "X" m0) env') in Hex.
        apply Bool.orb_false_iff in Hex. destruct Hex as [H_eq Hex'].
        cbn [Sem.buscar_variable]. destruct (string_dec "X" m) as [e | e].
        + apply String.eqb_eq in e. rewrite e in H_eq. discriminate H_eq.
        + apply IH. exact Hex'.
      }
      rewrite H_none in H.
      cbn in H.
      discriminate H.
	Qed.

(*
  Demostración formal de un for que incrementa X hasta 3.
  AST del programa:
    Precondición: X=0 en el entorno inicial

    for {} lt(X, 3) {} { X := add(X, 1) }

  Postcondición: X ≥ 3 en el entorno final.
*)

(*Precondición: X declarada antes del bucle con valor 0 *)
Definition P (e : FranAST.yul_env) (fe : FranAST.yul_fun_env) (s : FranEVM_Dialect_ext.dialect_state_t) : Prop :=
  exists val, Sem.buscar_variable "X"%string e = Some val /\ U32.val val = 0%Z.

Definition init   := ([] : list FranAST.yul_expr).
Definition cond   := FranAST.YulOp EVM_opcode.LT (FranAST.YulVar "X"%string :: FranAST.YulConst (U32.to_t 3%Z) :: nil).
Definition post   := ([] : list FranAST.yul_expr).
Definition cuerpo := FranAST.YulAsignar ("X"%string :: nil)
                 (FranAST.YulOp EVM_opcode.ADD
                   (FranAST.YulVar "X"%string :: FranAST.YulConst (U32.to_t 1%Z) :: nil)) :: nil.

(*Invariante: existe un valor val en X tal que val < 3*)
Definition I (e : FranAST.yul_env) (fe : FranAST.yul_fun_env) (s : FranEVM_Dialect_ext.dialect_state_t) : Prop :=
  exists val rest_e marker_val, 
    e = ("|"%string, marker_val) :: rest_e /\ 
    Sem.buscar_variable "X"%string rest_e = Some val /\ 
    (0<=U32.val val <= 3)%Z.

(*Postcondición: existe un valor val en X tal que val >= 3*)
Definition Q (e : FranAST.yul_env) (fe : FranAST.yul_fun_env) (s : FranEVM_Dialect_ext.dialect_state_t) : Prop :=
  exists val, Sem.buscar_variable "X"%string e = Some val /\ U32.val val >= 3%Z.

(*
  La prueba utiliza el lema hoare_for de hoare.v:
  - H    : init establece I
  - Hcond: cond verdadera implica I
  - Hfalse: cond falsa implica Q
  - Hbreak: el cuerpo no produce break
  - Hbreak': el post no produce break
  - H'   : el cuerpo y el post mantienen I
*)

Theorem for_example :
  {{ P }}
    FranAST.YulFor init cond post cuerpo
  {{ Q }}.
Proof.
  eapply hoare_for with (I := I).
  - (* Hinit *)
    intros env_pre fenv_pre state_pre HP f env_in fenv_in state_in res env_out fenv_out state_out Heval Heq.
    destruct HP as [val_x [Hvar_x Hval_x]].
    destruct Heq as [Heq_env [Heq_fenv Heq_state]]. subst.
    rec_fuel_en Heval. simpl in Heval. inversion Heval; subst.
    exists val_x.
    exists env_pre.
    exists FranEVM_Dialect_ext.default_value. 
    split. { unfold FranEVM_Dialect_ext.default_value. reflexivity. }
    split. { exact Hvar_x. } { lia. }
  - (* Hcond *)
    intros f e fe s rc ec fec sc HI Hc.
    destruct HI as [val_x [rest_e [marker_val [Heq [Hvar Hval]]]]]. subst e.
    rec_fuel_en Hc. simpl in Hc. rewrite Hvar in Hc.
    inversion Hc; subst.
    exists val_x.
    exists rest_e.
    exists marker_val. 
    split. { reflexivity. } 
    split. { exact Hvar. } { exact Hval. }
  - (* Hfalse *)
    intros f e fe s rc ec fec sc HI Hc Hf.
    destruct HI as [val_x [rest_e [marker_val [Heq [Hvar Hval]]]]]. subst e.
    rec_fuel_en Hc. simpl in Hc. rewrite Hvar in Hc.
    inversion Hc; subst.
    unfold Sem.is_true, FranEVM_Dialect_ext.is_true_value, U32.lt in Hf.
    destruct (U32.val val_x <? U32.val (U32.to_t 3%Z))%Z eqn:Hlt.
    + simpl in Hf. discriminate Hf.
    + apply Z.ltb_ge in Hlt. change (U32.val (U32.to_t 3%Z)) with 3%Z in Hlt.
      exists val_x. split.
      * simpl. exact Hvar.
      * (*
          Hlt: 3<= U32.val val_x, y el objetivo a probar es U32.val val_x >=3.
          No se puede aplicar "exact Hlt" por ser tener '<=' y '>=' definiciones
          inductivas distintas, pese a tener el mismo significado -> se aplica lia. 
      *)
        lia.
  - (* Hbreak *)
    intros f rc ec fec sc rb eb feb sb HI H_rc Hbreak.
    destruct HI as [val_x [rest_e [marker_val [Heq [Hvar Hval]]]]]. subst ec.
    rec_fuel_en Hbreak. simpl in Hbreak. rewrite Hvar in Hbreak.
    unfold Sem.actualizar_vars in Hbreak. simpl in Hbreak. rewrite Hvar in Hbreak.
    rec_fuel_en Hbreak. simpl in Hbreak. inversion Hbreak.
  - (* H' *)
    intros f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp.
    intros H_I H_cond H_rc H_ctrlb H_cuerpo H_post H_ctrlp.
    destruct H_I as [val_x [rest_e [marker_val [Heq [Hvar Hval]]]]]. subst e_i.
    rec_fuel_en H_cond. simpl in H_cond. rewrite Hvar in H_cond. inversion H_cond; subst.
    rec_fuel_en H_post. simpl in H_post. inversion H_post; subst.
    rec_fuel_en H_cuerpo. simpl in H_cuerpo. rewrite Hvar in H_cuerpo.
    unfold Sem.actualizar_vars in H_cuerpo. simpl in H_cuerpo. rewrite Hvar in H_cuerpo.
    rec_fuel_en H_cuerpo. simpl in H_cuerpo. inversion H_cuerpo; subst.
    simpl.
    exists (U32.add val_x (U32.to_t 1%Z)).
    exists (Sem.reemplazar_var "X"%string (U32.add val_x (U32.to_t 1%Z)) rest_e).
    exists marker_val.
    split. { reflexivity. }
    split.
    + eapply Sem.buscar_reemplazar_mismo. exact Hvar.
    + unfold Sem.is_true, FranEVM_Dialect_ext.is_true_value, U32.lt in H_rc.
      change (U32.val (U32.to_t 3%Z)) with 3%Z in H_rc.
      destruct (U32.val val_x <? 3)%Z eqn:Hlt_b in H_rc.
      * unfold U32.add, U32.to_t, U32.modulus in *.
        simpl in *. 
        replace (Z.pow_pos 2 32) with 4294967296%Z in * by reflexivity.
        replace (1 mod 4294967296%Z) with 1%Z in * by reflexivity.
        apply Z.ltb_lt in Hlt_b.
        rewrite Z.mod_small; lia.
      * discriminate H_rc.
Qed.
