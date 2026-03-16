open Cil_types

(* 
  The intermediate representation for the contract logic
*)

exception ArmException of string

type no_overflow_type = Oadd | Osub | Omul | Odiv

type arm_predicate =
  (* false *)
  | Afalse
  (* true *)
  | Atrue
  (* p1 ⇔ p2 *)
  | Aiff of arm_predicate * arm_predicate
  (* if c then p1 else p2, TODO make this into a predicate and always use ints? *)
  | Aif of arm_term * arm_predicate * arm_predicate
  (* p1 ∧ p2 *)
  | Aand of arm_predicate * arm_predicate
  (* p1 ∨ p2 *)
  | Aor of arm_predicate * arm_predicate
  (* p1 ⇒ p2 *)
  | Aimplies of arm_predicate * arm_predicate
  (* ¬p *)
  | Anot of arm_predicate
  (* p1 ^^ p2 *)
  | Axor of arm_predicate * arm_predicate
  (* t1 (<, >, ≤, ≥, =, ≠) t2 *)
  | Arel of relation * arm_term * arm_term
  (* ================================ TODO ================================ *)
  (* overflow t1 (+, -, *, /) t2 *)
  | Aoverflow of no_overflow_type * arm_term * arm_term
  (* p_fresh *)
  | Aunknown

and arm_term = arm_term_node
and arm_logic_var = string
and arm_word_size = Word8 | Word16 | Word32 | Word64

(** base address of an lvalue. *)
and arm_term_lhost =
  (* a variable. *)
  | AVar of arm_logic_var
  (* REG(s, register, size) *)
  | ARegister of int * arm_word_size
  (* MEM(s, pointer, size) *)
  | AMemory of arm_term * arm_word_size

and arm_term_offset =
  (* no further offset. *)
  | ANoOffset
  (* index. Note that a range is denoted by [TIndex(Trange(i1,i2),ofs)] *)
  | AIndex of arm_term * arm_term_offset

and arm_term_lval = arm_term_lhost * arm_term_offset
and arm_logic_constant = ABoolean of bool | AInteger of string

and arm_term_node =
  (* a constant. *)
  | AConst of arm_logic_constant
  (* an L-value *)
  | ALval of arm_term_lval
  (* Stack pointer *)
  | SP
  (* lhs (+, -, *, /, %, <<, >>, <, >, <=, >=, ==, !=, &, ^, |) rhs *)
  | ABinOp of binop * arm_term * arm_term
  (* cast to a C type (if bool is false)
      or an implicit conversion from C type to a logic type (if bool is true).
      In the second case:
      The logic type must not be a Ctype.
      In particular, used to denote lifting to Linteger and Lreal.
  *)
  | ACast of bool * logic_type * arm_term

type arm_overflow = arm_predicate option
type arm_location = Pre | Post

type arm_enviroment = {
  mutable result : arm_term option;
  mutable pre_variables : (arm_term * arm_logic_var) list;
  mutable old : (arm_term * arm_logic_var) list;
}

type arm_contract = {
  ensures : arm_predicate;
  requires : arm_predicate;
  enviroment : arm_enviroment;
}

type contract_printer = { fmt : Format.formatter }
(*type contract_options = { overflow : bool }*)

(* If we can simplify it, then do it. This is just an ad hoc solution to simplify trivial expressions intoduced in folding *)
let rec simplify (predicate : arm_predicate) : arm_predicate =
  match predicate with
  | Aand (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Atrue, Atrue -> Atrue
      | Afalse, _ | _, Afalse -> Afalse
      | Atrue, _ -> simplify p2
      | _, Atrue -> simplify p1
      | _, _ -> Aand (simplify p1, simplify p2))
  | Aor (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Afalse, Afalse -> Afalse
      | Atrue, _ | _, Atrue -> Atrue
      | Afalse, _ -> simplify p2
      | _, Afalse -> simplify p1
      | _, _ -> Aor (simplify p1, simplify p2))
  | Anot p -> (
      match simplify p with
      | Afalse -> Atrue
      | Atrue -> Afalse
      | pattern -> Anot pattern)
  | Aiff (lhs, rhs) -> (
      match (simplify lhs, simplify rhs) with
      | Afalse, Afalse -> Atrue
      | Atrue, Atrue -> Afalse
      | pattern_lhs, pattern_rhs -> Aiff (pattern_lhs, pattern_rhs))
  | Aif (c, p1, p2) -> Aif (c, simplify p1, simplify p2)
  | Aimplies (p1, p2) -> Aimplies (simplify p1, simplify p2)
  | Axor (p1, p2) -> Axor (simplify p1, simplify p2)
  | _ -> predicate
