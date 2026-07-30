Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import ZArith.ZArith.

Require Import LenguajeYul.dialect.
Require Import main.fran_dialect.
Require Import main.fran_dialect_parser.
Require Import main.ast.
Require Import main.semantica.

Module AST := YulAST FranEVM_Dialect_ext.
Module Sem := YulSemantica FranEVM_Dialect_ext AST.

Open Scope string_scope.
Open Scope Z_scope.

(* Helper definitions for testing *)
Definition v (z : Z) : FranEVM_Dialect_ext.value_t := U32.to_t z.
Definition state0 : FranEVM_Dialect_ext.dialect_state_t := FranEVM_Dialect_ext.empty_dialect_state.
Definition f_max : nat := 100.

(* 1. Pruebas de Instrucciones Básicas *)

(* YulConst *)
Example test_const :
  Sem.eval_yul f_max (AST.YulConst (v 42)) [] [] state0 false =
  ([v 42], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulVar *)
Example test_var_ok :
  Sem.eval_yul f_max (AST.YulVar "X") [("X", v 10)] [] state0 false =
  ([v 10], [("X", v 10)], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

Example test_var_fail :
  Sem.eval_yul f_max (AST.YulVar "Y") [("X", v 10)] [] state0 false =
  ([], [("X", v 10)], [], state0, Sem.Yul_Error "Variable no definida: Y").
Proof. reflexivity. Qed.

(* YulLet *)
Example test_let :
  Sem.eval_yul f_max (AST.YulLet ["X"] (AST.YulConst (v 5))) [] [] state0 false =
  ([], [("X", v 5)], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulAsignar *)
Example test_asignar :
  Sem.eval_yul f_max (AST.YulAsignar ["X"] (AST.YulConst (v 20))) [("X", v 5)] [] state0 false =
  ([], [("X", v 20)], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulOp *)
Example test_op :
  Sem.eval_yul f_max (AST.YulOp EVM_opcode.ADD [AST.YulConst (v 2); AST.YulConst (v 3)]) [] [] state0 false =
  ([v 5], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* 2. Pruebas de Control de Flujo *)

(* YulBlock *)
Example test_block :
  Sem.eval_yul f_max (AST.YulBlock [AST.YulLet ["X"] (AST.YulConst (v 5))]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulIf *)
Example test_if_true :
  Sem.eval_yul f_max (AST.YulIf (AST.YulConst (v 1)) [AST.YulLet ["X"] (AST.YulConst (v 5))]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

Example test_if_false :
  Sem.eval_yul f_max (AST.YulIf (AST.YulConst (v 0)) [AST.YulLet ["X"] (AST.YulConst (v 5))]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulSwitch *)
Example test_switch_match :
  Sem.eval_yul f_max (AST.YulSwitch (AST.YulConst (v 1)) [(v 1, [AST.YulLet ["Y"] (AST.YulConst (v 2))])] []) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

Example test_switch_default :
  Sem.eval_yul f_max (AST.YulSwitch (AST.YulConst (v 3)) [(v 1, [AST.YulLet ["Y"] (AST.YulConst (v 2))])] [AST.YulLet ["Z"] (AST.YulConst (v 4))]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.

(* YulBreak and YulContinue *)
Example test_break :
  Sem.eval_yul f_max AST.YulBreak [] [] state0 true =
  ([], [], [], state0, Sem.Yul_Break).
Proof. reflexivity. Qed.

Example test_continue :
  Sem.eval_yul f_max AST.YulContinue [] [] state0 true =
  ([], [], [], state0, Sem.Yul_Continue).
Proof. reflexivity. Qed.

(* YulLeave *)
Example test_leave :
  Sem.eval_yul f_max AST.YulLeave [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Leave).
Proof. reflexivity. Qed.

(* 3. Pruebas de Scoping y Entornos *)

(* No Shadowing *)
Example test_shadowing_fail :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulLet ["x"] (AST.YulConst (v 1));
    AST.YulBlock [
      AST.YulLet ["x"] (AST.YulConst (v 2))
    ]
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable ya declarada o numero de variables no coincide con los valores que devuelve la funcion").
Proof. reflexivity. Qed.

(* Function Execution Scoping *)
(* Declaramos 'x' fuera, e intentamos leerla dentro de la función 'f' que es llamada. *)
Example test_fun_scope :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulLet ["x"] (AST.YulConst (v 10));
    AST.YulFunc "f" [] ["ret"] [
      AST.YulAsignar ["ret"] (AST.YulVar "x")
    ];
    AST.YulLet ["y"] (AST.YulCall "f" [])
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable no definida: x").
Proof. reflexivity. Qed.

(* Shadowing in For loop body *)
Example test_shadowing_for_fail :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulLet ["x"] (AST.YulConst (v 1));
    AST.YulFor [] (AST.YulConst (v 1)) [] [
      AST.YulLet ["x"] (AST.YulConst (v 2))
    ]
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable ya declarada o numero de variables no coincide con los valores que devuelve la funcion").
Proof. reflexivity. Qed.

(* Shadowing in Switch case *)
Example test_shadowing_switch_fail :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulLet ["x"] (AST.YulConst (v 1));
    AST.YulSwitch (AST.YulConst (v 1)) [(v 1, [AST.YulLet ["x"] (AST.YulConst (v 2))])] []
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable ya declarada o numero de variables no coincide con los valores que devuelve la funcion").
Proof. reflexivity. Qed.

(* Function trying to assign to outer variable *)
Example test_fun_assign_outer_fail :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulLet ["x"] (AST.YulConst (v 10));
    AST.YulFunc "f" [] [] [
      AST.YulAsignar ["x"] (AST.YulConst (v 5))
    ];
    AST.YulLet ["y"] (AST.YulCall "f" [])
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable no definida o número de valores incorrecto").
Proof. reflexivity. Qed.

(* Function trying to declare variable with same name as parameter *)
Example test_fun_shadow_param_fail :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulFunc "f" ["a"] [] [
      AST.YulLet ["a"] (AST.YulConst (v 5))
    ];
    AST.YulLet ["y"] (AST.YulCall "f" [AST.YulConst (v 10)])
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Error "Variable ya declarada o numero de variables no coincide con los valores que devuelve la funcion").
Proof. reflexivity. Qed.

(* Valid Function Call *)
Example test_fun_valid :
  Sem.eval_yul f_max (AST.YulBlock [
    AST.YulFunc "f" ["a"] ["ret"] [
      AST.YulAsignar ["ret"] (AST.YulOp EVM_opcode.ADD [AST.YulVar "a"; AST.YulConst (v 5)])
    ];
    AST.YulLet ["y"] (AST.YulCall "f" [AST.YulConst (v 10)])
  ]) [] [] state0 false =
  ([], [], [], state0, Sem.Yul_Running).
Proof. reflexivity. Qed.
