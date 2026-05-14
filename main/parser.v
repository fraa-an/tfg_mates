From Stdlib Require Import Strings.String.
Open Scope string_scope.
From Stdlib Require Import Ascii.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.
Require Import main.fran_dialect.
Require Import LenguajeYul.dialect.

Inductive yul_expr :=
  | YulConst (v : U32.t) 
  | YulOp (op : EVM_opcode.t) (args : list yul_expr)
  | YulLet (nombres: list string) (valor: yul_expr)
  | YulVar (nombre_var : string)
  | YulIf (cond : yul_expr) (inst : list yul_expr)
  | YulSwitch (cond : yul_expr) (casos : list (U32.t * list yul_expr)) (default : list yul_expr)
  | YulFor (ini : list yul_expr) (cond : yul_expr) (post : list yul_expr) (inst : list yul_expr)
  | YulFunc (nombre : string) (params : list string) (ret : list string) (inst : list yul_expr)
  | YulCall (nombre : string) (args : list yul_expr).

Record yul_funcion := {
  f_params  : list string;
  f_ret : list string;
  f_inst   : list yul_expr
}.
Definition yul_fun_env := list (string * yul_funcion).
Definition yul_env := list (string * U32.t).

Definition is_true (l : list U32.t) : bool :=
  match l with
  | val :: _ => negb (U32.eqb val U32.zero)
  | nil => false
  end.

Definition lista_strings (s : string) : list ascii :=
  let fix f s :=
    match s with
    | ""%string => []
    | String c s' => c :: f s'
    end in f s.

Definition es_espacio (c : ascii) : bool :=
  match nat_of_ascii c with
  | 32%nat | 9%nat | 10%nat | 13%nat => true 
  | _ => false
  end.

Definition es_simbolo (c : ascii) : bool :=
  match c with
  | "(" | ")" | "," | "}" | "{" => true
  | _ => false
  end%char.

Definition es_salto_linea (c : ascii) : bool :=
  match nat_of_ascii c with
  | 10%nat | 13%nat => true (*10: salto de línea, 13: retorno de carro *)
  | _ => false
  end.

Fixpoint strip_comentarios (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | "/"%char :: "/"%char :: resto => strip_linea resto
  | "/"%char :: "*"%char :: resto => strip_multilinea resto
  | c :: resto => 
    if Nat.eqb (nat_of_ascii c) 34 
    then c :: strip_string resto
    else c :: strip_comentarios resto
  end
with strip_linea (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | c :: resto =>
    if es_salto_linea c 
    then c :: strip_comentarios resto
    else strip_linea resto   
  end
with strip_multilinea (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | "*"%char :: "/"%char :: resto => strip_comentarios resto 
  | _ :: resto => strip_multilinea resto                
  end
with strip_string (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | c :: resto =>
    if Nat.eqb (nat_of_ascii c) 92 (* 92: '\' *)
    then 
      match resto with
      | [] => [c]
      | c2 :: resto2 => c :: c2 :: strip_string resto2 
      end
    else if Nat.eqb (nat_of_ascii c) 34 
    then c :: strip_comentarios resto
    else c :: strip_string resto
  end.

Fixpoint tokeniza_aux (s : list ascii) (palabra_actual : string) : list string :=
  match s with
  | [] => if Nat.ltb 0 (String.length palabra_actual) then [palabra_actual] else []
  | ":"%char :: "="%char :: resto =>
    let simb := ":="%string in
    let cola := tokeniza_aux resto "" in
    if Nat.ltb 0 (String.length palabra_actual) then palabra_actual :: simb :: cola else simb :: cola
  | "-"%char :: ">"%char :: resto =>
    let simb := "->"%string in
    let cola := tokeniza_aux resto "" in
    if Nat.ltb 0 (String.length palabra_actual) then palabra_actual :: simb :: cola else simb :: cola
  | c :: resto =>
    if es_espacio c then
      let cola := tokeniza_aux resto "" in
      if Nat.ltb 0 (String.length palabra_actual) then palabra_actual :: cola else cola
    else if es_simbolo c then
      let simb := String c "" in
      let cola := tokeniza_aux resto "" in
      if Nat.ltb 0 (String.length palabra_actual) then palabra_actual :: simb :: cola else simb :: cola
    else
      tokeniza_aux resto (palabra_actual ++ String c "")
  end.

Definition tokeniza (s : string) : list string :=
  let chars := lista_strings s in
  let chars_sin_com := strip_comentarios chars in
  tokeniza_aux chars_sin_com "".

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



Definition char_to_nat (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if (Nat.leb 48 n) && (Nat.leb n 57) then Some (n - 48)%nat else None.

Definition hex_char_to_Z (c : ascii) : option Z :=
  match c with
  | "0" => Some 0%Z | "1" => Some 1%Z | "2" => Some 2%Z | "3" => Some 3%Z
  | "4" => Some 4%Z | "5" => Some 5%Z | "6" => Some 6%Z | "7" => Some 7%Z
  | "8" => Some 8%Z | "9" => Some 9%Z
  | "a" | "A" => Some 10%Z | "b" | "B" => Some 11%Z
  | "c" | "C" => Some 12%Z | "d" | "D" => Some 13%Z
  | "e" | "E" => Some 14%Z | "f" | "F" => Some 15%Z
  | _ => None
  end%char.
Fixpoint parsea_nat_aux (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c rest =>
      match char_to_nat c with
      | Some d => parsea_nat_aux rest (acc * 10 + d)
      | None => None 
      end
  end.
Fixpoint parsea_hex_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
      match hex_char_to_Z c with
      | Some v => parsea_hex_aux s' (Z.add (Z.mul 16%Z acc) v)
      | None => None
      end
  end.

Definition parsea_hex (s : string) : option U32.t :=
  match parsea_hex_aux s 0%Z with
  | Some z => Some (U32.to_t z) 
  | None => None
  end.
Definition parsea_nat (s : string) : option nat :=
  match s with
  | EmptyString => None
  | _ => parsea_nat_aux s 0
  end.

Definition parsea_uint32 (s : string) : option U32.t :=
  match parsea_nat s with
  | Some n => Some (U32.to_t (Z.of_nat n))
  | None => None
  end.
Fixpoint parsea_ascii_aux (f: nat) (s : string) (acc : Z) : option Z :=
  match f with 
  | O => None 
  | S f' =>
      match s with
      | EmptyString => Some acc
      | String "\" (String "x" (String c1 (String c2 s'))) =>
          match hex_char_to_Z c1, hex_char_to_Z c2 with
          | Some v1, Some v2 => 
              let char_val := Z.add (Z.mul 16%Z v1) v2 in
              parsea_ascii_aux f' s' (Z.add (Z.mul 256%Z acc) char_val)
          | _, _ => None
          end
      | String "\" (String "u" (String c1 (String c2 (String c3 (String c4 s'))))) =>
          match hex_char_to_Z c1, hex_char_to_Z c2, hex_char_to_Z c3, hex_char_to_Z c4 with
          | Some v1, Some v2, Some v3, Some v4 => 
              let val1 := Z.add (Z.mul 16%Z v1) v2 in
              let val2 := Z.add (Z.mul 16%Z v3) v4 in
              let char_val := Z.add (Z.mul 256%Z val1) val2 in
              parsea_ascii_aux f' s' (Z.add (Z.mul 65536%Z acc) char_val)
          | _, _, _, _ => None
          end
      | String c s' =>
          let char_val := Z.of_nat (nat_of_ascii c) in
          parsea_ascii_aux f' s' (Z.add (Z.mul 256%Z acc) char_val)
      end
  end.

Definition parsea_ascii (s : string) : option U32.t :=
  match parsea_ascii_aux 100 s 0%Z with
  | Some z => Some (U32.to_t z)
  | None => None
  end.
Definition es_prefijo (prefijo s : string) : bool :=
  let len_p := String.length prefijo in
  if Nat.leb len_p (String.length s) then
    if string_dec prefijo (substring 0 len_p s) then true else false
  else false.

Definition parsea_literal (tok : string) : option U32.t :=
  if es_prefijo "0x" tok then
     parsea_hex (substring 2 (String.length tok - 2) tok)
  else if es_prefijo "hex""" tok then
     parsea_hex (substring 4 (String.length tok - 5) tok)
  else if es_prefijo """" tok then
     parsea_ascii (substring 1 (String.length tok - 2) tok)
  else
     parsea_uint32 tok.


Fixpoint parsea_idents (f : nat) (tokens : list string) {struct f} : option (list string * list string) :=
  match f with
  | O => None
  | S f' =>
      match tokens with
      | ")"%string :: _ => Some ([], tokens)
      | "{"%string :: _ => Some ([], tokens)
      | "->"%string :: _ => Some ([], tokens)
      | tok :: ","%string :: resto =>
          match parsea_idents f' resto with
          | Some (ids, resto2) => Some (tok :: ids, resto2)
          | None => None
          end
      | tok :: resto => Some ([tok], resto)
      | [] => None
      end
  end.

Fixpoint parsea_expr (f : nat) (tokens : list string) {struct f} : option (yul_expr * list string) :=
  match f with
  | O => None
  | S f' =>
      match tokens with
      | [] => None
      | "function"%string :: nom :: "("%string :: resto =>
          match parsea_idents f' resto with
          | Some (params, ")"%string :: "->"%string :: resto2) =>
              match parsea_idents f' resto2 with
              | Some (rets, resto3) =>
                  match parsea_bloque f' resto3 with
                  | Some (cuerpo, resto4) => Some (YulFunc nom params rets cuerpo, resto4)
                  | None => None
                  end
              | None => None
              end
          | Some (params, ")"%string :: resto2) =>
              match parsea_bloque f' resto2 with
              | Some (cuerpo, resto3) => Some (YulFunc nom params [] cuerpo, resto3)
              | None => None
              end
          | _ => None
          end
      | "let"%string :: resto =>
          match parsea_idents f' resto with
          | Some (nombres, ":="%string :: resto_expr) =>
              match parsea_expr f' resto_expr with
              | Some (expr_valor, tokens_sobrantes) => Some (YulLet nombres expr_valor, tokens_sobrantes)
              | None => None
              end
          | _ => None
          end
      | "if"%string :: resto =>
          match parsea_expr f' resto with
          | Some (cond, resto1) =>
              match parsea_bloque f' resto1 with
              | Some (cuerpo, resto2) => Some (YulIf cond cuerpo, resto2)
              | None => None
              end
          | None => None
          end
          
      | "for"%string :: resto =>
          match parsea_bloque f' resto with
          | Some (init, resto1) =>
              match parsea_expr f' resto1 with
              | Some (cond, resto2) =>
                  match parsea_bloque f' resto2 with
                  | Some (post, resto3) =>
                      match parsea_bloque f' resto3 with
                      | Some (cuerpo, resto4) => Some (YulFor init cond post cuerpo, resto4)
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
          
      | "switch"%string :: resto =>
          match parsea_expr f' resto with
          | Some (cond, resto1) =>
              match parsea_casos f' resto1 with
              | Some (casos, resto2) =>
                  match resto2 with
                  | "default"%string :: resto3 =>
                      match parsea_bloque f' resto3 with
                      | Some (def, resto4) => Some (YulSwitch cond casos def, resto4)
                      | None => None
                      end
                  | _ => Some (YulSwitch cond casos [], resto2)
                  end
              | None => None
              end
          | None => None
          end
      | _ =>
        match parsea_idents f' tokens with
        | Some (nombres, ":="%string :: resto_expr) =>
            match parsea_expr f' resto_expr with
           | Some (expr_valor, tokens_sobrantes) => Some (YulLet nombres expr_valor, tokens_sobrantes)
           | None => None
           end
        | _ =>
          match tokens with
          | t :: rest =>
              match string_a_opcode t with
              | Some op => 
                  match rest with
                  | "("%string :: rest2 => 
                      match parsea_args f' rest2 with
                      | Some (args, ")"%string :: rest4) => Some (YulOp op args, rest4)
                      | _ => None
                      end
                  | _ => None
                  end
              | None => 
                  match parsea_literal t with
                  | Some val => Some (YulConst val, rest)
                  | None => 
                      match rest with
                      | "("%string :: rest2 => 
                          match parsea_args f' rest2 with
                          | Some (args, ")"%string :: rest4) => Some (YulCall t args, rest4)
                          | _ => None
                          end
                      | _ => 
                          Some (YulVar t, rest)
                      end
                  end
              end
            | [] => None
            end
        end       
    end
  end
with parsea_args (f : nat) (tokens : list string) {struct f} : option (list yul_expr * list string) :=
  match f with
  | O => None
  | S f' =>
      match parsea_expr f' tokens with
      | Some (expr, ","%string :: rest2) =>
          match parsea_args f' rest2 with
          | Some (next_args, rest3) => Some (expr :: next_args, rest3)
          | None => None
          end
      | Some (expr, rest) => Some ([expr], rest)
      | None => Some ([], tokens)
      end
  end

with parsea_bloque (f : nat) (tokens : list string) {struct f} : option (list yul_expr * list string) :=
  match f with
  | O => None
  | S f' =>
      match tokens with
      | "{"%string :: resto => parsea_instrucciones f' resto
      | _ => None
      end
  end

with parsea_instrucciones (f : nat) (tokens : list string) {struct f} : option (list yul_expr * list string) :=
  match f with
  | O => None
  | S f' =>
      match tokens with
      | "}"%string :: resto => Some ([], resto) (* Fin del bloque *)
      | [] => None
      | _ => 
          match parsea_expr f' tokens with
          | Some (expr, resto1) =>
              match parsea_instrucciones f' resto1 with
              | Some (exprs, resto2) => Some (expr :: exprs, resto2)
              | None => None
              end
          | None => None
          end
      end
  end

with parsea_casos (f : nat) (tokens : list string) {struct f} : option (list (U32.t * list yul_expr) * list string) :=
  match f with
  | O => None
  | S f' =>
      match tokens with
      | "case"%string :: val_str :: resto =>
          match parsea_uint32 val_str with
          | Some val =>
              match parsea_bloque f' resto with
              | Some (cuerpo, resto2) =>
                  match parsea_casos f' resto2 with
                  | Some (otros_casos, resto3) => Some ((val, cuerpo) :: otros_casos, resto3)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | _ => Some ([], tokens)
      end
  end.

Fixpoint buscar_variable (nombre : string) (env : yul_env) : option U32.t :=
  match env with
  | [] => None
  | (n, v) :: resto =>
      if string_dec nombre n then Some v 
      else buscar_variable nombre resto
  end.

Fixpoint buscar_funcion (nom : string) (fenv : yul_fun_env) : option yul_funcion :=
  match fenv with
  | [] => None
  | (n, f) :: resto => if string_dec nom n then Some f else buscar_funcion nom resto
  end.

Fixpoint combinar_params (nombres : list string) (valores : list U32.t) : yul_env :=
  match nombres, valores with
  | n :: ns, v :: vs => (n, v) :: combinar_params ns vs
  | _, _ => []
  end.

Fixpoint eval_yul (f : nat) (expr : yul_expr) (env : yul_env) (fenv: yul_fun_env) (state : EVMState.t) {struct f} : (list U32.t * yul_env * yul_fun_env * EVMState.t * Status.t) :=
  match f with
  | O => ([], env, fenv, state, Status.Error "error")
  | S f' => 
    match expr with
    | YulConst v => ([v], env, fenv, state, Status.Running)
    | YulOp op args =>
      let '(vals, env_final, fenv_final, s_final, st) := eval_argumentos f' args env fenv state in
      match st with
      | Status.Running => 
        let '(res, s_r, status) := EVMDialect.execute_opcode s_final op vals in 
        (res, env_final, fenv_final, s_r, status)
      | _ => ([], env_final, fenv_final, s_final, st)
      end
    | YulLet nombres var_expr =>
      let '(valores, env_i, fenv_i, state_i, st) := eval_yul f' var_expr env fenv state in
      match st with
      | Status.Running =>
          let fix asignar_multiples (ns : list string) (vs : list U32.t) (e : yul_env) : option yul_env :=
            match ns, vs with
            | [], [] => Some e
            | n::ns', v::vs' => asignar_multiples ns' vs' ((n, v) :: e)
            | _, _ => None 
            end
          in
          match asignar_multiples nombres valores env_i with
          | Some nuevo_env => ([], nuevo_env, fenv_i, state_i, Status.Running)
          | None => ([], env_i, fenv_i, state_i, Status.Error "El numero de variables no coincide con los valores que devuelve la funcion")
          end
      | _ => (valores, env_i, fenv_i, state_i, st)
      end
    | YulVar nom =>
      match buscar_variable nom env with
      | Some v => ([v], env, fenv, state, Status.Running)
      | None => ([], env, fenv, state, Status.Error ("Variable no definida: " ++ nom))
      end
    | YulIf cond inst =>
      let '(res, env1, fenv1, state1, status1) := eval_yul f' cond env fenv state in
          match status1 with
          | Status.Running => 
              if (is_true res) 
              then eval_list f' inst env1 fenv1 state1
              else ([], env1, fenv1, state1, Status.Running)
          | _ => (res, env1, fenv1, state1, status1)
          end
    | YulFunc nom params rets inst =>
      let n_func := {| f_params := params; f_ret := rets; f_inst := inst |} in
      ([], env, (nom, n_func) :: fenv, state, Status.Running)
    | YulSwitch cond casos def =>
      let '(res_c, env_c, fenv_c, state_c, status_c) := eval_yul f' cond env fenv state in
      match status_c with
      | Status.Running =>
          let fix buscar_caso (l : list (U32.t * list yul_expr)) :=
            match l with
            | nil => eval_list f' def env_c fenv_c state_c
            | (val_caso, cuerpo) :: resto =>
                let v_evaluado := match res_c with 
                                  | v :: _ => v 
                                  | nil => U32.zero 
                                  end in
                if U32.eqb v_evaluado val_caso
                then eval_list f' cuerpo env_c fenv_c state_c
                else buscar_caso resto
            end
          in buscar_caso casos
      | _ => (res_c, env_c, fenv_c, state_c, status_c)
      end
    | YulFor init cond post cuerpo =>
      let '(res_i, env_i, fenv_i, state_i, status_i) := eval_list f' init env fenv state in
      match status_i with
      | Status.Running =>
        let fix bucle n e fe s :=
        match n with
        | O => ([], e, fe, s, Status.Error "error en For")
        | S n' =>
          let '(res_c, e_c, fe_c, s_c, status_c) := eval_yul n' cond e fe s in
            match status_c with
            | Status.Running =>
              if is_true res_c then
                let '(_, e_b, fe_b, s_b, status_b) := eval_list n' cuerpo e_c fe_c s_c in
                  match status_b with
                  | Status.Running => 
                    let '(_, e_p, fe_p, s_p, status_p) := eval_list n' post e_b fe_b s_b in
                      match status_p with
                      | Status.Running => bucle n' e_p fe_p s_p
                      | fallo => ([], e_p, fe_p, s_p, fallo)
                      end
                  | fallo => ([], e_b, fe_b, s_b, fallo)
                  end
              else ([], e_c, fe_c, s_c, Status.Running)
            | fallo => ([], e_c, fe_c, s_c, fallo)
            end
        end
        in bucle f' env_i fenv_i state_i
      | fallo => (res_i, env_i, fenv_i, state_i, fallo)
      end
    | YulCall nom args =>
      let '(vals, env_a, fenv_a, state_a, st) := eval_argumentos f' args env fenv state in
      match st with
      | Status.Running =>
        match buscar_funcion nom fenv_a with
        | Some func =>
          let env_local := combinar_params (f_params func) vals in
            eval_list f' (f_inst func) env_local fenv_a state_a
        | None => ([], env_a, fenv_a, state_a, Status.Error ("Función no definida: " ++ nom))
        end
      | _ => ([], env_a, fenv_a, state_a, st)
      end
    end
  end
with eval_list (f : nat) (l : list yul_expr) (env : yul_env) (fenv : yul_fun_env) (state : EVMState.t) {struct f}: (list U32.t * yul_env * yul_fun_env * EVMState.t * Status.t) :=
  match f with
  | O => ([], env, fenv, state, Status.Error "error")
  | S f' =>
      match l with
      | nil => ([], env, fenv, state, Status.Running)
      | e :: rest =>
          let '(res, env1, fenv1, state1, status1) := eval_yul f' e env fenv state in
          match status1 with
          | Status.Running => eval_list f' rest env1 fenv1 state1
          | _ => (res, env1, fenv1, state1, status1)
          end
      end
  end
with eval_argumentos (f : nat) (l : list yul_expr) (e : yul_env) (fe : yul_fun_env) (s : EVMState.t) {struct f}: (list U32.t * yul_env * yul_fun_env * EVMState.t * Status.t) :=
  match f with
  | O => ([], e, fe, s, Status.Error "Out of fuel en argumentos")
  | S f' =>
    match l with
    | [] => ([], e, fe, s, Status.Running)
    | x :: xs => 
      let '(res, e', fe', s', st) := eval_yul f' x e fe s in
      match st with
      | Status.Running => 
        let '(rest, e'', fe'', s'', st') := eval_argumentos f' xs e' fe' s' in
        match st' with
        | Status.Running => ((res ++ rest)%list, e'', fe'', s'', Status.Running)
        | _ => ([], e'', fe'', s'', st')
        end
      | _ => ([], e', fe', s', st)
      end
    end
  end.

Definition ejecutar_eval_bloque (ast_list : list yul_expr) (env : yul_env) (fenv : yul_fun_env) (state : EVMState.t) : (list U32.t * yul_env * yul_fun_env * EVMState.t * Status.t) :=
  eval_list 5000 ast_list env fenv state.

Definition eval_programa (s : string) : (list U32.t * yul_env * yul_fun_env * EVMState.t * Status.t) :=
  match parsea_bloque 100 (tokeniza s) with
  | Some (ast_list, _) => ejecutar_eval_bloque ast_list [] [] EVMState.empty
  | None => ([], [], [], EVMState.empty, Status.Error "Error de parseo")
  end.