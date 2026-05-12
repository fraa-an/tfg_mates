Require Import Strings.String.
Require Import Ascii.
Require Import Lists.List.
Require Import Bool.
Require Import ZArith.
Import ListNotations.
Require Import main.fran_dialect.
Require Import LenguajeYul.dialect.

Inductive yul_expr :=
  | YulConst (v : U32.t) 
  | YulOp (op : EVM_opcode.t) (args : list yul_expr).

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
  | "(" | ")" | "," => true
  | _ => false
  end%char.

Fixpoint tokeniza_aux (s : list ascii) (palabra_actual : string) : list string :=
  match s with
  | [] => if Nat.ltb 0 (String.length palabra_actual) then [palabra_actual] else []
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
  tokeniza_aux (lista_strings s) "".

Definition string_a_opcode (s : string) : option EVM_opcode.t :=
  if string_dec s "add" then Some EVM_opcode.ADD 
  (**string_dec sirve para comprobar igualdad de strings**)
  else if string_dec s "sub" then Some EVM_opcode.SUB
  else if string_dec s "mul" then Some EVM_opcode.MUL
  else if string_dec s "div" then Some EVM_opcode.DIV
  else None.


Definition char_to_nat (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if (Nat.leb 48 n) && (Nat.leb n 57) then Some (n - 48)%nat else None.

Fixpoint parsea_nat_aux (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c rest =>
      match char_to_nat c with
      | Some d => parsea_nat_aux rest (acc * 10 + d)
      | None => None (* Falla si encuentra letras o símbolos *)
      end
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

Fixpoint parsea_expr (tokens : list string) (l: nat) : option (yul_expr * list string) :=
  match l with
  | O => None
  | S f =>
      match tokens with
      | [] => None
      | t :: rest =>
          match string_a_opcode t with
          | Some op => 
              match rest with
              | "(" :: rest2 => 
                  match parsea_args rest2 f with
                  | Some (args, rest3) =>
                      match rest3 with
                      | ")" :: rest4 => Some (YulOp op args, rest4)
                      | _ => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | None => 
              match parsea_uint32 t with
              | Some val => Some (YulConst val, rest)
              | None => None
              end
          end
      end
  end

with parsea_args (tokens : list string) (i : nat) : option (list yul_expr * list string) :=
  match i with
  | O => None
  | S f =>
      match parsea_expr tokens f with
      | Some (expr, rest) =>
          match rest with
          | "," :: rest2 => 
              match parsea_args rest2 f with
              | Some (next_args, rest3) => Some (expr :: next_args, rest3)
              | None => None
              end
          | _ => Some ([expr], rest)
          end
      | None => Some ([], tokens)
      end
  end.

Fixpoint eval_yul (expr : yul_expr) (state : EVMState.t) : (list U32.t * EVMState.t * Status.t) :=
  match expr with
  | YulConst v => ([v], state, Status.Running)
  | YulOp op args =>
      let fix eval_list l s :=
        match l with
        | [] => Some ([], s)
        | e :: es => 
            match eval_yul e s with
            | (res, s', Status.Running) => 
                match eval_list es s' with
                | Some (rest, s'') => Some ((res ++ rest)%list, s'')
                | None => None
                end
            | _ => None
            end
        end in
      match eval_list args state with
      | Some (vals, s_final) => EVMDialect.execute_opcode s_final op vals
      | None => ([], state, Status.Error "Error evaluando argumentos")
      end
  end.