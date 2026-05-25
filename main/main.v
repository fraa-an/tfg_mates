From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
Require Import LenguajeYul.dialect.
Require Import main.fran_dialect.
Require Import main.ast.
Require Import main.semantica.
Require Import main.parser.

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
Module EVM_Semantics := YulSemantica FranEVM_Dialect_ext FranAST.
    
Definition evaluar_evm (s : string) :=
    match EVM_Parser.parse_programa s with
    | Some ast => 
        EVM_Semantics.ejecutar_eval_bloque ast nil nil FranEVM_Dialect_ext.empty_dialect_state
    | None => 
        (nil, nil, nil, FranEVM_Dialect_ext.empty_dialect_state, Status.Error "Error de sintaxis")
    end.

Compute evaluar_evm "{
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