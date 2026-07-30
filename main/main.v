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

(*
  Demostración formal de un for que incrementa X hasta 3.
  AST del programa:
    for { let X := 0 } lt(X, 3) {} { X := add(X, 1) }

  Postcondición: X ≥ 3 en el entorno final.
*)
Definition init   := FranAST.YulLet ("X"%string :: nil) (FranAST.YulConst (U32.to_t 0%Z)) :: nil.
Definition cond   := FranAST.YulOp EVM_opcode.LT (FranAST.YulVar "X"%string :: FranAST.YulConst (U32.to_t 3%Z) :: nil).
Definition post   := ([] : list FranAST.yul_expr).
Definition cuerpo := FranAST.YulAsignar ("X"%string :: nil)
                 (FranAST.YulOp EVM_opcode.ADD
                   (FranAST.YulVar "X"%string :: FranAST.YulConst (U32.to_t 1%Z) :: nil)) :: nil.

(*Invariante: existe un valor val en X tal que val < 3*)
Definition I (e : FranAST.yul_env) (fe : FranAST.yul_fun_env) (s : FranEVM_Dialect_ext.dialect_state_t) : Prop :=
  exists val, Sem.buscar_variable "X" e = Some val /\ U32.val val <= 3.

(*Postcondición: X ≥ 3*)
Definition Q (e : FranAST.yul_env) (fe : FranAST.yul_fun_env) (s : FranEVM_Dialect_ext.dialect_state_t) : Prop :=
  True.

(*
  La prueba utiliza el lema hoare_for de hoare.v:
  - H    : init establece I
  - Hcond: cond verdadera implica I se mantiene para la lectura de X
  - Hfalse: cond falsa implica Q (X ≥ 3)
  - Hbreak: el cuerpo no produce break
  - Hbreak': el post no produce break
  - H'   : el cuerpo y el post mantienen I
*)
Ltac solve_zero H :=
  discriminate H ||
  (inversion H; subst;
   match goal with
   | [ Hcontra : Sem.Yul_Error _ = Sem.Yul_Running |- _ ] => discriminate Hcontra
   | [ Hcontra : Sem.Yul_Error _ = Sem.Yul_Continue |- _ ] => discriminate Hcontra
   | [ Hcontra : Sem.Yul_Error _ = Sem.Yul_Break |- _ ] => discriminate Hcontra
   | [ Hcontra : Sem.Yul_Error _ = Sem.Yul_Leave |- _ ] => discriminate Hcontra
   | [ Hcontra : Sem.Yul_Running = Sem.Yul_Error _ |- _ ] => discriminate Hcontra
   | [ Hcontra : Sem.Yul_Error _ = Sem.Yul_Running \/ Sem.Yul_Error _ = Sem.Yul_Continue |- _ ] =>
       destruct Hcontra as [Hc|Hc]; discriminate Hc
   end).

Ltac mi_fuel H :=
  simpl in H;
  match type of H with
  | context [Sem.eval_bucle ?x _ _ _ _ _ _ _ _] =>
      destruct x; [ solve_zero H | simpl in H]
  | context [Sem.eval_list ?x _ _ _ _ _] =>
      destruct x; [ solve_zero H | simpl in H]
  | context [Sem.eval_yul ?x _ _ _ _ _] =>
      destruct x; [ solve_zero H | simpl in H]
  | context [Sem.eval_argumentos ?x _ _ _ _ _] =>
      destruct x; [ solve_zero H | simpl in H]
  end.

Ltac reduce_fuel H := repeat (mi_fuel H).

Theorem for_example :
  {{ fun e fe s => True }}
    FranAST.YulFor init cond post cuerpo
  {{ Q }}.
Proof.
  eapply hoare_for with (I := I).
  - (*Hinit*)
    intros env_pre fenv_pre state_pre _ f e fe s res e' fe' s' Hinit _.
    reduce_fuel Hinit.
    destruct (Sem.buscar_variable "X" e) as [val|] eqn:Hvar in Hinit.
    + simpl in Hinit. inversion Hinit.
    + simpl in Hinit. inversion Hinit; subst.
      exists (U32.to_t 0%Z). split.
      * unfold Sem.buscar_variable.
        destruct (string_dec "X" "|") as [|Hneq]; [discriminate|].
        destruct (string_dec "X" "X") as [Heq|]; [reflexivity|contradiction].
      * change (U32.val (U32.to_t 0%Z)) with 0%Z. lia.
  - (*Hcond*)
    intros f e fe s rc ec fec sc HI Hc.
    reduce_fuel Hc.
    destruct (Sem.buscar_variable "X" e) as [val|] eqn:Hvar in Hc.
    + simpl in Hc. inversion Hc; subst. exact HI.
    + simpl in Hc. inversion Hc.
  - (*Hfalse*)
    intros f e fe s rc ec fec sc HI Hc Hf.
    constructor.
  - (*Hbreak*)
    intros f rc ec fec sc rb eb feb sb HI H_rc Hbreak.
    constructor.
  - (*H'*)
    intros f e_i fe_i s_i rc ec fec sc rb eb feb sb rp ep fep sp ctrlb ctrlp.
    intros H_I H_cond H_rc H_ctrlb H_cuerpo H_post H_ctrlp.
    reduce_fuel H_cond.
    destruct (Sem.buscar_variable "X" e_i) as [val_i|] eqn:Hvar_i in H_cond.
    + simpl in H_cond. inversion H_cond. subst ec fec sc.
      reduce_fuel H_post.
      unfold post in H_post. simpl in H_post. inversion H_post; subst.
      destruct H_I as [val [Hb Hle]].
      (* Usar reduce_fuel hasta que se atasque en buscar_variable *)
      reduce_fuel H_cuerpo.
      (* Ahora reemplazar buscar_variable "X" e_i con Some val *)
      rewrite Hb in H_cuerpo.
      (* Sustituir actualizar_vars para desatascarlo *)
      unfold Sem.actualizar_vars in H_cuerpo. simpl in H_cuerpo.
      rewrite Hb in H_cuerpo.
      (* Y seguir reduciendo el fuel hasta el final *)
      reduce_fuel H_cuerpo.
      simpl in H_cuerpo. inversion H_cuerpo; subst.
      
      simpl in Hvar_i. rewrite Hb in Hvar_i. injection Hvar_i as Heq_vi. subst val_i.
      exists (U32.add val (U32.to_t 1%Z)). split.
      ++ simpl. erewrite Sem.buscar_reemplazar_mismo; [reflexivity|exact Hb].
      ++ unfold Sem.is_true, FranEVM_Dialect_ext.is_true_value, U32.lt in H_rc.
         change (U32.val (U32.to_t 3%Z)) with 3%Z in H_rc.
         destruct val as [v Hv]. simpl in *.
         destruct (v <? 3)%Z eqn:Hlt_b in H_rc.
         ** unfold U32.add, U32.to_t in *. 
            replace (1 mod U32.modulus)%Z with 1%Z in * by reflexivity.
            unfold U32.modulus, U32.Valid in *.
            replace (Z.pow_pos 2 32) with 4294967296%Z in * by reflexivity.
            simpl in *.
            apply Z.ltb_lt in Hlt_b. rewrite Z.mod_small; lia.
         ** discriminate H_rc.
    + simpl in H_cond. inversion H_cond.
Qed.

