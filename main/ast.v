From Stdlib Require Import Strings.String.
Require Import LenguajeYul.dialect.

Module Type AST_INTERFACE (D : DIALECT).
  Inductive yul_expr : Type :=
    | YulConst (v : D.value_t) 
    | YulOp (op : D.opcode_t) (args : list yul_expr)
    | YulLet (nombres: list string) (valor: yul_expr)
    | YulVar (nombre_var : string)
    | YulIf (cond : yul_expr) (inst : list yul_expr)
    | YulSwitch (cond : yul_expr) (casos : list (D.value_t * list yul_expr)) (default : list yul_expr)
    | YulFor (ini : list yul_expr) (cond : yul_expr) (post : list yul_expr) (inst : list yul_expr)
    | YulFunc (nombre : string) (params : list string) (ret : list string) (inst : list yul_expr)
    | YulCall (nombre : string) (args : list yul_expr)
    | YulBreak
    | YulContinue
    | YulLeave.

  Record yul_funcion_r := {
    f_params  : list string;
    f_ret : list string;
    f_inst   : list yul_expr
  }.
  
  Definition yul_funcion := yul_funcion_r.
  Definition yul_fun_env := list (string * yul_funcion).
  Definition yul_env := list (string * D.value_t).
End AST_INTERFACE.

Module YulAST (D : DIALECT) <: AST_INTERFACE D.

  Inductive yul_expr : Type :=
    | YulConst (v : D.value_t) 
    | YulOp (op : D.opcode_t) (args : list yul_expr)
    | YulLet (nombres: list string) (valor: yul_expr)
    | YulVar (nombre_var : string)
    | YulIf (cond : yul_expr) (inst : list yul_expr)
    | YulSwitch (cond : yul_expr) (casos : list (D.value_t * list yul_expr)) (default : list yul_expr)
    | YulFor (ini : list yul_expr) (cond : yul_expr) (post : list yul_expr) (inst : list yul_expr)
    | YulFunc (nombre : string) (params : list string) (ret : list string) (inst : list yul_expr)
    | YulCall (nombre : string) (args : list yul_expr)
    | YulBreak
    | YulContinue
    | YulLeave.

  Record yul_funcion_r := {
    f_params  : list string;
    f_ret : list string;
    f_inst   : list yul_expr
  }.
  
  Definition yul_funcion := yul_funcion_r.
  Definition yul_fun_env := list (string * yul_funcion).
  Definition yul_env := list (string * D.value_t).
End YulAST.
 