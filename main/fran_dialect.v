From Stdlib Require Strings.String.
From Stdlib Require Lists.List.
From Stdlib Require Ascii.
Open Scope string_scope.
Require Import LenguajeYul.dialect.
Require Import LenguajeYul.misc.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Strings.HexString.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Bool.

Open Scope Z_scope.

Module U32.

  Definition modulus := 2^32.
  
  Definition Valid (val: Z): Prop :=
    0 <= val < modulus.
  
  (* The Type Definition. It includes the value and a proposition stating its validity *)
  Record t := mk {
    val : Z;
    is_valid : Valid val
  }.

  Definition eqb (x y: t): bool :=
    Z.eqb (val x) (val y).

  (* we require boolean equality to reflect equality *)
  Lemma eqb_spec : forall x y : t, reflect (x = y) (eqb x y).
  Proof.
    intros x y.
    unfold eqb.

    destruct (Z.eqb_spec (val x) (val y)) as [Heq | Hneq].

    - apply ReflectT.
      destruct x as [vx px], y as [vy py].
      simpl in Heq.
      subst vy.
      f_equal.
      apply proof_irrelevance.

    - apply ReflectF.
      intro H_assume_equal.
      rewrite H_assume_equal in Hneq.
      contradiction.
  Defined.
  
  (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y, eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: t, eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (eqb_spec x y).
  Defined.
  
  
  (* A constructor that takes any Z and fits it into t *)
  Program Definition to_t (z : Z) : t :=
    mk (z mod modulus) _.
  Next Obligation.
    apply Z.mod_pos_bound.
    vm_compute. reflexivity.
  Defined.

  Definition zero: t := to_t 0.
  Definition one: t := to_t 1.
  Definition two_to_31: t := to_t (2^31).
  
  
  Definition of_bool (b: bool): U32.t :=
    if b then one else zero.

  (* Inspired by Stdlib module of
     https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L408*)
  Definition get_signed_value (value: U32.t): Z :=
    (((val value) + (2 ^ 31)) mod (2 ^ 32)) - (2 ^ 31).

  Definition add (a b: U32.t): U32.t :=
    to_t ( (val a) + (val b) ).

  Definition sub (a b: U32.t): U32.t :=
    to_t ( (val a) - (val b) ).

  Definition mul (a b: U32.t): U32.t :=
    to_t ( (val a) * (val b) ).

  Definition div (a b: U32.t): U32.t :=
    if (val b) =? 0 then zero else to_t (Z.div (val a) (val b)).

  Definition sdiv (x y: U32.t): U32.t :=
      if (val y) =? 0 then zero
      else
        let zx := get_signed_value x in
        let zy := get_signed_value y in
        to_t (zx / zy).

  Lemma val_mod_valid : forall (x y : t), 
    val y <> 0 -> 0 <= (val x mod val y) < modulus.
  Proof.
    intros x y Hneq.
    assert (Hbound := Z.mod_pos_bound (val x) (val y)).
    destruct (is_valid y) as [Hlow Hhigh].
    assert (Hpos : 0 < val y).
    { apply Z.lt_eq_cases in Hlow.
      destruct Hlow as [Hlt | Heq].
      - exact Hlt.
      - symmetry in Heq; contradiction. }
    destruct (Z.mod_pos_bound (val x) (val y) Hpos) as [Hlow_mod Hhigh_mod].
    split.
    - exact Hlow_mod.
    - apply Z.lt_trans with (m := val y).
      + exact Hhigh_mod.
      + exact Hhigh.
  Qed.

  Definition mod_evm (x y: U32.t): U32.t :=
    match Z.eq_dec (val y) 0 with
    | left _ => zero
    |  right Hneq =>
        mk (val x mod val y) (val_mod_valid x y Hneq)
    end.
    
  Definition smod (x y: U32.t): U32.t :=
      if (val y) =? 0 then zero
      else
        let x := get_signed_value x in
        let y := get_signed_value y in
        to_t (x mod y).
    
  Definition exp (x y: U32.t): U32.t :=
      to_t ((val x) ^ (val y)).

  Definition not (x: U32.t): U32.t :=
      to_t (2^32 - (val x) - 1).

  Definition lt (x y: U32.t): U32.t :=
      if (val x) <? (val y) then one else zero.

  Definition gt (x y: U32.t): U32.t :=
    if (val x) >? (val y) then one else zero.

  (* Signed version of [lt] *)
  Definition slt (x y: U32.t): U32.t :=
    let x := get_signed_value x in
    let y := get_signed_value y in
    if x <? y then one else zero.
  
  Definition sgt (x y: U32.t): U32.t :=
    let x := get_signed_value x in
    let y := get_signed_value y in
    if x >?  y then one else zero.

  Definition eq (x y: U32.t): U32.t :=
    if (val x) =? (val y) then one else zero.
  
  Definition iszero (x: U32.t): U32.t :=
    if (val x) =? 0 then one else zero.
  
  Definition and (x y: U32.t): U32.t :=
    to_t (Z.land (val x) (val y)). (* this could be improved to eliminate the call to to_t *)

  Definition or (x y: U32.t): U32.t :=
    to_t (Z.lor (val x) (val y)).

  Definition xor (x y: U32.t): U32.t :=
    to_t (Z.lxor (val x) (val y)).

  Definition byte (n x: U32.t): U32.t := (* SHL and MOD 6 *)
    to_t ( ( (val x) / (32 ^ (31 - (val n)))) mod 32). (* this could be improved to eliminate the call to to_t *)

  Definition shl (x y: U32.t): U32.t :=
    to_t ((val y) * (2 ^ (val x))).

  Definition shr (x y: U32.t): U32.t :=
    to_t ((val y) / (2 ^ (val x))). (* this could be improved to eliminate the call to to_t *)

  Definition sar (shift value: U32.t): U32.t :=
    let signed_value := get_signed_value value in
    let shifted_value := signed_value / (2 ^ (val shift)) in
    to_t shifted_value.


  (** Count the number of constructors in a positive number *)
  Fixpoint _count_constructors_pos (p: positive): nat :=
    match p with
    | xH => 1
    | xO p' => S (_count_constructors_pos p')
    | xI p' => S (_count_constructors_pos p')
    end.

  (** Count the number of constructors in a Z value *)
  Definition _count_constructors_Z (z: Z): nat :=
    match z with
    | Z0 => 0
    | Zpos p => _count_constructors_pos p
    | Zneg p => _count_constructors_pos p
    end.

  Definition clz (x: U32.t): U32.t :=
    let x_val := val x in
    let len := Z.of_nat (_count_constructors_Z x_val) in
    to_t (32 - len). 

  Definition addmod (x y m: U32.t): U32.t :=
    to_t ( ((val x) + (val y)) mod (val m) ). (* this could be improved to eliminate the call to to_t *)

  Definition mulmod (x y m: U32.t): U32.t :=
   to_t ( ((val x) * (val y)) mod (val m)). (* this could be improved to eliminate the call to to_t *)

    (* From https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L549 *)
  Definition signextend (ai ax: U32.t): U32.t :=
    let i := (val ai) in
    let x := (val ax) in
    if i >=? 31 then ax
    else
      let size := 8 * (i + 1) in
      let byte := (x / 2 ^ (8 * i)) mod 32 in
      let sign_bit := byte / 128 in
      let extend_bit (bit size: Z): Z := if bit =? 1 then (2 ^ 32) - (2 ^ size) else 0 in
      to_t ((x mod (2 ^ size)) + extend_bit sign_bit size). (* this could be improved to eliminate the call to to_t *)

End U32.


(* A byte *)
Module U8.

  Definition modulus := 2^8.
  
  Definition Valid (val: Z): Prop :=
    0 <= val < modulus.

  
  (* The Type Definition. It includes the value and a proposition stating its validity *)
  Record t := mk {
    val : Z;
    is_valid : Valid val
  }.

  (* A constructor that takes any Z and fits it into t *)
  Program Definition to_t (z : Z) : t :=
    mk (z mod modulus) _.
  Next Obligation.
    apply Z.mod_pos_bound.
    vm_compute. reflexivity.
  Defined.

  Definition zero: t := to_t 0.
  Definition one: t := to_t 1.

End U8.

Module EVMStorage.
  (* From github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  Definition t: Set :=
    U32.t -> U32.t.

  Definition empty: t :=
    fun _ => U32.zero.

  Definition update (storage: EVMStorage.t) (address value: U32.t): EVMStorage.t :=
    fun current_address =>
      if U32.eqb address current_address then value
      else storage current_address.
End EVMStorage.


Module EVMMemory.
  (** From 
      github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  (** We define the memory as a function instead of an explicit list as there can be holes in it. It
      goes from addresses in [U32.t] to bytes represented as [Z]. *)
  Record t : Type := {
    memory : U32.t -> U8.t;
    highest_address: U32.t; (* this is used to track the highest address that has been accessed, which is needed for MSIZE instruction *)
  }.

  Definition empty: t := {|
    memory := fun _ => U8.zero;
    highest_address := U32.zero
  |}.

  Definition msize (memory: t): U32.t :=
    (* The size is always a multiple of a word (32 bytes) *)
    let size := memory.(highest_address) in
    if U32.eqb size U32.zero then U32.zero
    else
      let remainder := U32.mod_evm size (U32.to_t 32) in
      if U32.eqb remainder U32.zero then size
      else U32.add size (U32.sub (U32.to_t 32) remainder).

  Definition update_highest_address (memory: t) (address: U32.t): t :=
    match U32.eqb (U32.gt address memory.(highest_address)) U32.one with
    | true => {| memory := EVMMemory.memory memory; 
                 highest_address := address 
              |}
    | false => memory
    end.

  Definition update_memory (memory: t) (new_memory: U32.t -> U8.t): t :=
    {| memory := new_memory; 
       highest_address := memory.(highest_address) 
    |}.

  (** Get the bytes from some memory from a start address and for a certain length. *)
  Definition get_bytes (memoryt: EVMMemory.t) (start length: U32.t): (list U8.t * EVMMemory.t) :=
    let bytes : list U8.t := List.map
      (fun (i: nat) =>
         let address: U32.t := U32.to_t ((U32.val start) + Z.of_nat i) in (* when reaching end of memory we start from 0 *)
         (EVMMemory.memory memoryt) address
      )
      (List.seq 0 (Z.to_nat (U32.val length))) in
    let memory := update_highest_address memoryt (U32.to_t ((U32.val start) + (U32.val length) - 1)) in
    (bytes, memory).

  Definition update_bytes (memoryt: EVMMemory.t) (start: U32.t) (bytes: list U8.t): EVMMemory.t :=
    let memory := fun address =>
      let i: Z := (U32.val address) - (U32.val start) in
      if andb (0 <=? i) (i <? Z.of_nat (List.length bytes)) then
        List.nth_default U8.zero bytes (Z.to_nat i)
      else
        (EVMMemory.memory memoryt) address in
    let m1 := update_highest_address memoryt (U32.to_t ((U32.val start) + Z.of_nat (List.length bytes) - 1)) in
    let m2 := update_memory m1 memory in
    m2.

  Definition U32_as_bytes (value: U32.t): list U8.t :=
    List.map
      (fun (i: nat) => U8.to_t (Z.shiftr (U32.val value) (8 * (31 - Z.of_nat i)) mod 32) )
      (List.seq 0 32).

  Fixpoint bytes_as_U32_aux (acc: Z) (bytes: list U8.t): U32.t :=
    match bytes with
    | [] => U32.to_t acc
    | byte :: bytes =>
      bytes_as_U32_aux
        (acc * 32 + (U8.val byte))
        bytes
    end.

  Definition bytes_as_U32 (bytes: list U8.t): U32.t :=
    bytes_as_U32_aux 0 bytes.

  (*
  Lemma bytes_as_U32_bounds (bytes: list U8.t):
    0 <= bytes_as_U32 bytes < 2 ^ (8 * Z.of_nat (List.length bytes)).
  Proof.
  Admitted.
   *)
  
  Fixpoint hex_string_as_bytes (hex_string: string): list U8.t :=
    match hex_string with
    | ""%string => []
    | String.String a "" => [] (* this case is unexpected *)
    | String.String a (String.String b rest) =>
      match HexString.ascii_to_digit a, HexString.ascii_to_digit b with
      | Some a, Some b =>
        let byte := 16 * Z.of_N a + Z.of_N b in
        (U8.to_t byte):: hex_string_as_bytes rest
      | _, _ => [] (* this case is unexpected *)
      end
    end.
End EVMMemory.


Module EVMMemorySegment.
  (** List of bytes represented as Z. *)
  Definition t: Type := list U8.t.
  Definition empty: t := [].

  Definition length (segment: t): U32.t :=
    U32.to_t (Z.of_nat (List.length segment)).

  (* Returns a list of 'n' bytes from 'start', 0 for bytes out of size *)
  Definition get_bytes (segment: t) (start n: U32.t): list U8.t :=
    List.map
      (fun i =>
         let index: Z := (U32.val start) + Z.of_nat i in
         if index <? Z.of_nat (List.length segment) then
           List.nth_default U8.zero segment (Z.to_nat index)
         else
           U8.zero
      )
      (List.seq 0 (Z.to_nat (U32.val n))).

  Definition get_word (segment: t) (start: U32.t): U32.t :=
    EVMMemory.bytes_as_U32 (get_bytes segment start (U32.to_t 32)).

  Definition hash (segment: t): U32.t :=
    (* TODO: compute actual hash *)
    U32.to_t 42.
    
End EVMMemorySegment.


Module EVMState.
  Record t: Type := {
    storage: EVMStorage.t;
    tstorage: EVMStorage.t; 
    memory: EVMMemory.t;
    call_data_seg: EVMMemorySegment.t;
    return_data_seg: EVMMemorySegment.t;
    gas: U32.t;
    address: U32.t;
    balance: U32.t -> U32.t;
    caller: U32.t;
    callvalue: U32.t;
    code: U32.t -> EVMMemorySegment.t;
    nonce: list U8.t;
    chainid: U32.t;
    basefee: U32.t;
    blobbasefee: U32.t;
    origin: U32.t;
    gasprice: U32.t;
    blockhash: U32.t -> U32.t;
    blobhash: U32.t -> U32.t;
    coinbase: U32.t;
    timestamp: U32.t;
    number: U32.t;
    difficulty: U32.t;
    gaslimit: U32.t;
  }.

  Definition empty: t :=
    {| 
      storage := EVMStorage.empty;
      tstorage := EVMStorage.empty;
      memory := EVMMemory.empty;
      call_data_seg := EVMMemorySegment.empty;
      return_data_seg := EVMMemorySegment.empty;
      gas := U32.zero;
      address := U32.zero;
      balance := fun _ => U32.zero;
      caller := U32.zero;
      callvalue := U32.zero;
      code := fun _ => EVMMemorySegment.empty;
      nonce := [];
      chainid := U32.zero;
      basefee := U32.zero;
      blobbasefee := U32.zero;
      origin := U32.zero;
      gasprice := U32.zero;
      blockhash := fun _ => U32.zero;
      blobhash := fun _ => U32.zero;
      coinbase := U32.zero;
      timestamp := U32.zero;
      number := U32.zero;
      difficulty := U32.zero;
      gaslimit := U32.zero;
    |}.

  Definition update_storage (state: t) (storage' : EVMStorage.t): t :=
  {| 
    storage := storage';
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg);
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_tstorage (state: t) (tstorage' : EVMStorage.t): t :=
  {| 
    storage := state.(storage);
    tstorage := tstorage';
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg);
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_memory (state: t) (memory' : EVMMemory.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := memory';
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_gas (state: t) (gas' : U32.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := gas';
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_code (state: t) (addr: U32.t) (ncode: EVMMemorySegment.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := fun a => if U32.eqb a addr then ncode else (state.(code) a);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_return_data (state: t) (return_data: EVMMemorySegment.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := return_data;
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition hash (l: list U8.t) : U32.t :=
  (* TODO Compute actual hash *)
    U32.to_t 42.

  Definition invoke (state: t) (gas to value argsOffset argsSize retOffset retSize: U32.t): (U32.t * list U8.t) :=
  (* TODO execute call *)
    (U32.to_t 42, []). (* return value and return data *)

End EVMState.


Module EVM_opcode.
  Inductive t :=
    | ADD
    | SUB
    | MUL
    | DIV
    | SDIV
    | MOD
    | SMOD
    | EXP
    | NOT
    | LT
    | GT
    | SLT
    | SGT
    | EQ
    | ISZERO
    | AND
    | OR
    | XOR
    | BYTE
    | SHL
    | SHR
    | SAR
    | CLZ
    | ADDMOD
    | MULMOD
    | SIGNEXTEND
    | MLOAD
    | MSTORE
    | SLOAD
    | SSTORE
    | CALLDATALOAD
    .
    
    Definition eq_dec: forall (a b: t), {a = b} + {a <> b}.
      Proof. decide equality. Defined.

    Definition eqb (a b: t): bool :=
      if eq_dec a b then true else false.
      

    Definition execute (state: EVMState.t) (op: t) (inputs: list U32.t): (list U32.t * EVMState.t * Status.t) :=
      match op with
      | ADD => match inputs with
               | [x; y] => ([U32.add x y], state, Status.Running)
               | _ => ([], state, Status.Error "ADD expects 2 inputs")
               end
      | SUB => match inputs with
               | [x; y] => ([U32.sub x y], state, Status.Running)
               | _ => ([], state, Status.Error "SUB expects 2 inputs")
               end
      | MUL => match inputs with
               | [x; y] => ([U32.mul x y], state, Status.Running)
               | _ => ([], state, Status.Error "MUL expects 2 inputs")
               end
      | DIV => match inputs with
               | [x; y] => ([U32.div x y], state, Status.Running)
               | _ => ([], state, Status.Error "DIV expects 2 inputs")
               end
      | SDIV => match inputs with
               | [x; y] => ([U32.sdiv x y], state, Status.Running)
               | _ => ([], state, Status.Error "SDIV expects 2 inputs")
               end   
      | MOD => match inputs with
               | [x; y] => ([U32.mod_evm x y], state, Status.Running)
               | _ => ([], state, Status.Error "MOD expects 2 inputs")
               end  
      | SMOD => match inputs with
               | [x; y] => ([U32.smod x y], state, Status.Running)
               | _ => ([], state, Status.Error "SMOD expects 2 inputs")
               end    
      | EXP => match inputs with
               | [x; y] => ([U32.exp x y], state, Status.Running)
               | _ => ([], state, Status.Error "EXP expects 2 inputs")
               end         
      | NOT => match inputs with
               | [x] => ([U32.not x], state, Status.Running)
               | _ => ([], state, Status.Error "NOT expects 1 input")
               end   
      | LT => match inputs with
               | [x; y] => ([U32.lt x y], state, Status.Running)
               | _ => ([], state, Status.Error "LT expects 2 inputs")
               end   
      | GT => match inputs with
               | [x; y] => ([U32.gt x y], state, Status.Running)
               | _ => ([], state, Status.Error "GT expects 2 inputs")
               end   
      | SLT => match inputs with
               | [x; y] => ([U32.slt x y], state, Status.Running)
               | _ => ([], state, Status.Error "SLT expects 2 inputs")
               end   
      | SGT => match inputs with
               | [x; y] => ([U32.sgt x y], state, Status.Running)
               | _ => ([], state, Status.Error "SGT expects 2 inputs")
               end   
      | EQ => match inputs with
               | [x; y] => ([U32.eq x y], state, Status.Running)
               | _ => ([], state, Status.Error "EQ expects 2 inputs")
               end   
      | ISZERO => match inputs with
               | [x] => ([U32.iszero x], state, Status.Running)
               | _ => ([], state, Status.Error "ISZERO expects 1 input")
               end   
      | AND => match inputs with
               | [x; y] => ([U32.and x y], state, Status.Running)
               | _ => ([], state, Status.Error "AND expects 2 inputs")
               end   
      | OR => match inputs with
               | [x; y] => ([U32.or x y], state, Status.Running)
               | _ => ([], state, Status.Error "OR expects 2 inputs")
               end   
      | XOR => match inputs with
               | [x; y] => ([U32.xor x y], state, Status.Running)
               | _ => ([], state, Status.Error "XOR expects 2 inputs")
               end   
      | BYTE => match inputs with
               | [n; x] => ([U32.byte n x], state, Status.Running)
               | _ => ([], state, Status.Error "BYTE expects 2 inputs")
               end  
      | SHL => match inputs with
               | [x; y] => ([U32.shl x y], state, Status.Running)
               | _ => ([], state, Status.Error "SHL expects 2 inputs")
               end   
      | SHR => match inputs with
               | [x; y] => ([U32.shr x y], state, Status.Running)
               | _ => ([], state, Status.Error "SHR expects 2 inputs")
               end   
      | SAR => match inputs with
               | [x; y] => ([U32.sar x y], state, Status.Running)
               | _ => ([], state, Status.Error "SAR expects 2 inputs")
               end    
      | CLZ => match inputs with
               | [x] => ([U32.clz x], state, Status.Running)
               | _ => ([], state, Status.Error "CLZ expects 1 input")
               end 
      | ADDMOD => match inputs with
               | [x; y; m] => ([U32.addmod x y m], state, Status.Running)
               | _ => ([], state, Status.Error "ADDMOD expects 3 inputs")
               end   
      | MULMOD => match inputs with
               | [x; y; m] => ([U32.mulmod x y m], state, Status.Running)
               | _ => ([], state, Status.Error "MULMOD expects 3 inputs")
               end   
      | SIGNEXTEND => match inputs with
               | [x; y] => ([U32.signextend x y], state, Status.Running)
               | _ => ([], state, Status.Error "SIGNEXTEND expects 2 inputs")
               end    
      | MLOAD => match inputs with
               | [addr] =>
                   let (bytes, mem') := EVMMemory.get_bytes state.(EVMState.memory) addr (U32.to_t 32) in
                   let v := EVMMemory.bytes_as_U32 bytes in
                   let state' := EVMState.update_memory state mem' in
                   ([v], state', Status.Running)
               | _ => ([], state, Status.Error "MLOAD expects 1 input")
               end
      | MSTORE => match inputs with
               | [addr; v] =>
                   let bytes := EVMMemory.U32_as_bytes v in
                   let mem' := EVMMemory.update_bytes state.(EVMState.memory) addr bytes in
                   let state' := EVMState.update_memory state mem' in
                   ([], state', Status.Running)
               | _ => ([], state, Status.Error "MSTORE expects 2 input")
               end
      | SLOAD => match inputs with
               | [addr] =>
                   let v := state.(EVMState.storage) addr in
                   ([v], state, Status.Running)
               | _ => ([], state, Status.Error "SLOAD expects 1 input")
               end
      | SSTORE => match inputs with
               | [addr; v] =>
                   let storage' := EVMStorage.update state.(EVMState.storage) addr v in
                   let state' := EVMState.update_storage state storage' in
                   ([], state', Status.Running)
               | _ => ([], state, Status.Error "SSTORE expects 2 input")
               end
      | CALLDATALOAD => match inputs with
               | [offset] =>
                   let v := EVMMemorySegment.get_word state.(EVMState.call_data_seg) offset in
                   ([v], state, Status.Running)
               | _ => ([], state, Status.Error "CALLDATALOAD expects 1 input")
               end
    end. 

    Definition show (op: t): string :=
      match op with
      | ADD => "ADD"
      | SUB => "SUB"
      | MUL => "MUL"
      | DIV => "DIV"
      | SDIV => "SDIV"
      | MOD => "MOD"
      | SMOD => "SMOD"
      | EXP => "EXP"
      | NOT => "NOT"
      | LT => "LT"
      | GT => "GT"
      | SLT => "SLT"
      | SGT => "SGT"
      | EQ => "EQ"
      | ISZERO => "ISZERO"
      | AND => "AND"
      | OR => "OR"
      | XOR => "XOR"
      | BYTE => "BYTE"
      | SHL => "SHL"
      | SHR => "SHR"
      | SAR => "SAR"
      | CLZ => "CLZ"
      | ADDMOD => "ADDMOD"
      | MULMOD => "MULMOD"
      | SIGNEXTEND => "SIGNEXTEND"
      | MLOAD => "MLOAD"
      | MSTORE => "MSTORE"
      | SLOAD => "SLOAD"
      | SSTORE => "SSTORE"
      | CALLDATALOAD => "CALLDATALOAD"
      end.

End EVM_opcode.


(*
Module Type BLOCK_CHAIN.
  Parameter get_addr: U32.t ->  U32.t.
End BLOCK_CHAIN.
Module EVMDialect (BC: BLOCK_CHAIN) <: DIALECT.

*)

Module FranEVM_Dialect <: DIALECT.
  Definition value_t := U32.t.

  Definition eqb := U32.eqb.
  Definition eqb_spec := U32.eqb_spec.

  Definition is_true_value (v: value_t): bool :=
    negb(U32.eqb v U32.zero). (* 0 or 1? *)

  Definition opcode_t := EVM_opcode.t.

  Definition dialect_state_t := EVMState.t.

  Definition default_value: value_t := U32.zero.

  Definition execute_opcode (state: dialect_state_t) (op: opcode_t) (inputs: list value_t): (list value_t * dialect_state_t * Status.t) :=
    EVM_opcode.execute state op inputs.

  Definition opcode_indep_state (op: opcode_t) := 
    match op with
    | EVM_opcode.ADD => true
    | EVM_opcode.SUB => true
    | EVM_opcode.MUL => true
    | EVM_opcode.DIV => true
    | EVM_opcode.SDIV => true
    | EVM_opcode.MOD => true
    | EVM_opcode.SMOD => true
    | EVM_opcode.EXP => true
    | EVM_opcode.NOT => true
    | EVM_opcode.LT => true
    | EVM_opcode.GT => true
    | EVM_opcode.SLT => true
    | EVM_opcode.SGT => true
    | EVM_opcode.EQ => true
    | EVM_opcode.ISZERO => true
    | EVM_opcode.AND => true
    | EVM_opcode.OR => true
    | EVM_opcode.XOR => true
    | EVM_opcode.BYTE => true
    | EVM_opcode.SHL => true
    | EVM_opcode.SHR => true
    | EVM_opcode.SAR => true
    | EVM_opcode.CLZ => true
    | EVM_opcode.ADDMOD => true
    | EVM_opcode.MULMOD => true
    | EVM_opcode.SIGNEXTEND => true
    | EVM_opcode.MLOAD => false
    | EVM_opcode.MSTORE => false
    | EVM_opcode.SLOAD => false
    | EVM_opcode.SSTORE => false
    | EVM_opcode.CALLDATALOAD => false
    end.

  Ltac solve_binary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 [|v1 args]]];
  (* We use [ | | | ] to explicitly handle the 4 cases created by the destruct above *)
  [ 
    (* Case: args = [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: args = [v] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: args = [v; v0] -> SUCCESS *)
    (exists [op v v0]; exists Status.Running; split; reflexivity)
  | (* Case: args = [v; v0; v1; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Ltac solve_unary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 rest]];
  [ (* Case: [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: [v] -> SUCCESS *)
    (exists [op v]; exists Status.Running; split; reflexivity)
  | (* Case: [v; v0; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Ltac solve_ternary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 [|v1 [|v2 rest]]]];
  [ (* Case: [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: [v] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: [v; v0] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: [v; v0; v1] -> SUCCESS *)
    (exists [op v v0 v1]; exists Status.Running; split; reflexivity)
  | (* Case: [v; v0; v1; v2; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Lemma evm_opcode_indep_state_snd: forall (op: opcode_t),
    opcode_indep_state op = true -> 
    forall (s1 s2: dialect_state_t) (args: list value_t), 
    exists (res: list value_t) (status: Status.t),
    execute_opcode s1 op args = (res, s1, status) /\
    execute_opcode s2 op args = (res, s2, status).
  Proof.
    unfold execute_opcode. intros op Hopcode s1 s2 args.
    destruct op; try (simpl in Hopcode; discriminate Hopcode).
    - solve_binary_op (U32.add) "ADD expects 2 inputs" args.
    - solve_binary_op (U32.sub) "SUB expects 2 inputs" args.
    - solve_binary_op (U32.mul) "MUL expects 2 inputs" args.
    - solve_binary_op (U32.div) "DIV expects 2 inputs" args.
    - solve_binary_op (U32.sdiv) "SDIV expects 2 inputs" args.
    - solve_binary_op (U32.mod_evm) "MOD expects 2 inputs" args.
    - solve_binary_op (U32.smod) "SMOD expects 2 inputs" args.
    - solve_binary_op (U32.exp) "EXP expects 2 inputs" args.
    - solve_unary_op (U32.not) "NOT expects 1 input" args.
    - solve_binary_op (U32.lt) "LT expects 2 inputs" args.
    - solve_binary_op (U32.gt) "GT expects 2 inputs" args.
    - solve_binary_op (U32.slt) "SLT expects 2 inputs" args.
    - solve_binary_op (U32.sgt) "SGT expects 2 inputs" args.
    - solve_binary_op (U32.eq) "EQ expects 2 inputs" args.
    - solve_unary_op (U32.iszero) "ISZERO expects 1 input" args.
    - solve_binary_op (U32.and) "AND expects 2 inputs" args.
    - solve_binary_op (U32.or) "OR expects 2 inputs" args.
    - solve_binary_op (U32.xor) "XOR expects 2 inputs" args.
    - solve_binary_op (U32.byte) "BYTE expects 2 inputs" args.
    - solve_binary_op (U32.shl) "SHL expects 2 inputs" args.
    - solve_binary_op (U32.shr) "SHR expects 2 inputs" args.
    - solve_binary_op (U32.sar) "SAR expects 2 inputs" args.
    - solve_unary_op (U32.clz) "CLZ expects 1 input" args.
    - solve_ternary_op (U32.addmod) "ADDMOD expects 3 inputs" args.
    - solve_ternary_op (U32.mulmod) "MULMOD expects 3 inputs" args. 
    - solve_binary_op (U32.signextend) "SIGNEXTEND expects 2 inputs" args.
  Qed.
      
  Definition opcode_indep_state_snd := evm_opcode_indep_state_snd.

  Definition empty_dialect_state: dialect_state_t :=
    EVMState.empty.

  Definition show_value (v: value_t): string :=
    Misc.z_to_string (v.(U32.val)).
  
  Definition show_opcode (op: opcode_t): string :=
    EVM_opcode.show op.
End FranEVM_Dialect.

Module EVMDialect_Facts := DialectFacts FranEVM_Dialect.