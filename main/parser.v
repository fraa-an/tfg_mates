From Stdlib Require Import Strings.String.
Open Scope string_scope.
From Stdlib Require Import Ascii.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.
Require Import LenguajeYul.dialect.
Require Import main.ast.


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

Module Type PARSER_DIALECT.
    Include DIALECT.
    Parameter string_a_opcode : string -> option opcode_t.
    Parameter parsea_literal : string -> option value_t.
End PARSER_DIALECT.

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

    Definition parsea_nat (s : string) : option nat :=
    match s with
    | EmptyString => None
    | _ => parsea_nat_aux s 0
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

    Definition es_prefijo (prefijo s : string) : bool :=
    let len_p := String.length prefijo in
    if Nat.leb len_p (String.length s) then
        if string_dec prefijo (substring 0 len_p s) then true else false
    else false.

Module YulParser (D : PARSER_DIALECT) (A : AST_INTERFACE D).
    Import A.

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

    Fixpoint parsea_expr (f : nat) (tokens : list string) {struct f} : option (A.yul_expr * list string) :=
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

        | "break"%string :: resto =>
            Some (YulBreak, resto)

        | "continue"%string :: resto =>
            Some (YulContinue, resto)

        | "leave"%string :: resto =>
            Some (YulLeave, resto)
            
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
                match D.string_a_opcode t with
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
                    match D.parsea_literal t with
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
    with parsea_args (f : nat) (tokens : list string) {struct f} : option (list A.yul_expr * list string) :=
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

    with parsea_bloque (f : nat) (tokens : list string) {struct f} : option (list A.yul_expr * list string) :=
    match f with
    | O => None
    | S f' =>
        match tokens with
        | "{"%string :: resto => parsea_instrucciones f' resto
        | _ => None
        end
    end

    with parsea_instrucciones (f : nat) (tokens : list string) {struct f} : option (list A.yul_expr * list string) :=
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

    with parsea_casos (f : nat) (tokens : list string) {struct f} : option (list (D.value_t * list A.yul_expr) * list string) :=
    match f with
    | O => None
    | S f' =>
        match tokens with
        | "case"%string :: val_str :: resto =>
            match D.parsea_literal val_str with
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

    Definition parse_programa (s : string) : option (list A.yul_expr) :=
    match parsea_bloque 100 (tokeniza s) with
    | Some (ast_list, []) => Some ast_list
    | _ => None
    end.

End YulParser.