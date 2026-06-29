From Stdlib Require Import Strings.String.
Require Import LenguajeYul.dialect.

Module Type AST_INTERFACE (D : DIALECT).
  (*Posibles expresiones de Yul*)
  Inductive yul_expr : Type :=
    (*Literales: números (en base 10 o hexadecimal), strings, true/false*)
    | YulConst (v : D.value_t) 
    (*Operaciones dependientes del dialecto*)
    | YulOp (op : D.opcode_t) (args : list yul_expr)
    (*Declaración de variables*)
    | YulLet (nombres: list string) (valor: yul_expr)
    (*Asignación a variables ya declaradas*)
    | YulAsignar (nombres: list string) (valor: yul_expr)
    | YulVar (nombre_var : string) (*Variables*)
    | YulIf (cond : yul_expr) (inst : list yul_expr) (*Condicionales*)
    | YulSwitch (cond : yul_expr) (casos : list (D.value_t * list yul_expr)) (default : list yul_expr) (*Switch*)
    | YulFor (ini : list yul_expr) (cond : yul_expr) (post : list yul_expr) (inst : list yul_expr) (*Bucle*)
    (*Declaración de función*)
    | YulFunc (nombre : string) (params : list string) (ret : list string) (inst : list yul_expr)
    | YulCall (nombre : string) (args : list yul_expr) (*Llamada a función ya declarada*)
    (*Bloque de código: las variables declaradas en su interior no existen fuera de él*)
    | YulBlock (inst : list yul_expr)
    | YulBreak
    | YulContinue
    | YulLeave.

  (*Una función tiene nombre/identificador, lista de parámetros requeridos y lista de variables que devuelve*)
  Record yul_funcion_r := {
      f_params  : list string;
      f_ret : list string;
      f_inst   : list yul_expr
    }.
  
  Definition yul_funcion := yul_funcion_r.
  Definition yul_fun_env := list (string * yul_funcion). (*Entorno de funciones declaradas*)
  Definition yul_env := list (string * D.value_t). (*Entorno de variables declaradas*)
End AST_INTERFACE.

(*Implementación de la interfaz*)
Module YulAST (D : DIALECT) <: AST_INTERFACE D.
  Inductive yul_expr : Type :=
    | YulConst (v : D.value_t) 
    | YulOp (op : D.opcode_t) (args : list yul_expr)
    | YulLet (nombres: list string) (valor: yul_expr)
    | YulAsignar (nombres: list string) (valor: yul_expr)
    | YulVar (nombre_var : string)
    | YulIf (cond : yul_expr) (inst : list yul_expr)
    | YulSwitch (cond : yul_expr) (casos : list (D.value_t * list yul_expr)) (default : list yul_expr)
    | YulFor (ini : list yul_expr) (cond : yul_expr) (post : list yul_expr) (inst : list yul_expr)
    | YulFunc (nombre : string) (params : list string) (ret : list string) (inst : list yul_expr)
    | YulCall (nombre : string) (args : list yul_expr)
    | YulBlock (inst : list yul_expr)
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
 