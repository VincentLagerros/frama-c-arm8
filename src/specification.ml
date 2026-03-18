open Cil_types

(* 
  The intermediate representation for the contract logic
*)

exception ArmException of string

type no_overflow_type = Oadd | Osub | Omul | Odiv [@@deriving eq]

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
[@@deriving eq]

and arm_type =
  (* Machine integer of signed + size, corresponding to Ctype TInt *)
  | AInt of bool * arm_word_size
  (* A boolean value, corresponding to Lboolean *)
  | ABool
  (* A pointer value, corresponding to Ctype TPtr *)
  | APtr of arm_type

and arm_term = { node : arm_term_node; ty : arm_type }
and arm_logic_var = string
and arm_word_size = Word8 | Word16 | Word32 | Word64 [@@deriving eq]

(** base address of an lvalue. *)
and arm_term_lhost =
  (* a variable. *)
  | AVar of arm_logic_var
  (* REG(s, register, size) *)
  | ARegister of int * arm_word_size
  (* MEM(s, pointer, size) *)
  | AMemory of arm_term * arm_word_size
[@@deriving eq]

and arm_term_lval = arm_term_lhost
and arm_logic_constant = ABoolean of bool | AInteger of string

and arm_binop =
  | APlusA  (** arithmetic + *)
  | AMinusA  (** arithmetic - *)
  | AMult  (** * *)
  | ADiv
      (** /
          @see <https://frama-c.com/download/frama-c-plugin-development-guide.pdf>
      *)
  | AMod
      (** %
          @see <https://frama-c.com/download/frama-c-plugin-development-guide.pdf>
      *)
  | AShiftlt  (** shift left *)
  | AShiftrt  (** shift right *)
  | ALt  (** < (arithmetic comparison) *)
  | AGt  (** > (arithmetic comparison) *)
  | ALe  (** <= (arithmetic comparison) *)
  | AGe  (** >= (arithmetic comparison) *)
  | AEq  (** == (arithmetic comparison) *)
  | ANe  (** != (arithmetic comparison) *)
  | ABAnd  (** bitwise and *)
  | ABXor  (** exclusive-or *)
  | ABOr  (** inclusive-or *)
  | ALAnd
      (** logical and. Unlike other operators, this one does not always evaluate
          both operands. If you want to keep it during normalization, you must
          set {!Kernel.LogicalOperators}. You can know if the current machine
          support them via {!Machine.use_logical_operators}. *)
  | ALOr
      (** logical or. Like [LAnd] this operator is removed unless
          {!Kernel.LogicalOperators} is set. *)

and arm_term_node =
  (* a constant. *)
  | AConst of arm_logic_constant
  (* an L-value *)
  | ALval of arm_term_lval
  (* Stack pointer *)
  | SP
  (* lhs (+, -, *, /, %, <<, >>, <, >, <=, >=, ==, !=, &, ^, |) rhs *)
  | ABinOp of arm_binop * arm_term * arm_term
  (* cast to a C type (if bool is false)
      or an implicit conversion from C type to a logic type (if bool is true).
      In the second case:
      The logic type must not be a Ctype.
      In particular, used to denote lifting to Linteger and Lreal.
  *)
  | ACast of bool * logic_type * arm_term
[@@deriving eq]

type arm_overflow = arm_predicate option
type arm_location = Pre | Post

type arm_enviroment = {
  mutable variables : (arm_logic_var, arm_term) Hashtbl.t;
  mutable old : (arm_logic_var * arm_term) list;
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

(* Helper to print with Printer for error messages*)
let pp_spec (f : Format.formatter -> 'a -> unit) (term : 'a) : string =
  let buf = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buf in
  f fmt term;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
