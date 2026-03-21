open Specification
open Translation
open Cil_types

(*
  Intermediate representation -> python z3 code for testing
*)

(* Returns the predicate to check if a term contains overflow *)
(*let rec no_overflow_of_term (term : term) : arm_predicate =
  match term.term_node with
  | TConst _ -> Atrue
  | TLval (_, _) -> Atrue (* TODO FIX *)
  | Tat (term, _) -> no_overflow_of_term term (* TODO FIX OLD *)
  | TCast (_, _, term) -> no_overflow_of_term term
  | TBinOp (op, lhs, rhs) ->
      Aand
        ( Aand (no_overflow_of_term lhs, no_overflow_of_term rhs),
          match op with
          | PlusA -> Aoverflow (Oadd, lhs, rhs)
          | MinusA -> Aoverflow (Osub, lhs, rhs)
          | Mult -> Aoverflow (Omul, lhs, rhs)
          | Div -> Aoverflow (Odiv, lhs, rhs)
          | _ -> raise (ArmException "Unknown no_overflow_of_term") )
  | _ -> raise (ArmException "Unknown no_overflow_of_term")
*)

(*
  
  | TLval (host, offset) -> pp_arm_lvalue out host offset
  | Tat (term, label) -> pp_arm_at out old term label
  | TCast (_is_implicit_conversion, _convert_to_type, term) 
  *)

(* TODO overflow? *)
let pp_arm_logical_constant (out : contract_printer)
    (constant : arm_logic_constant) =
  match constant with
  | ABoolean true -> Format.fprintf out.fmt "True"
  | ABoolean false -> Format.fprintf out.fmt "False"
  | AInteger z -> Format.fprintf out.fmt "%s" z

let pp_logic_var (out : contract_printer) (var : arm_logic_var) =
  Format.fprintf out.fmt "%s" var

let rec pp_arm_lvalue (out : contract_printer) (host : arm_term_lhost) =
  match host with
  | AVar v -> pp_logic_var out v
  | ARegister (at, _size) -> Format.fprintf out.fmt "REG[%d]" at
  | AMemory (at, _size) ->
      Format.fprintf out.fmt "MEM[";
      pp_arm_term out at;
      Format.fprintf out.fmt "]"
(*
  | _ -> raise (ArmException "Unknown pp_arm_lvalue")*)

and pp_arm_binop (out : contract_printer) (op : arm_binop) (lhs : arm_term)
    (rhs : arm_term) : unit =
  let infix =
    (* TODO bitwise operations on bitvectors! as z3 does not support bit operations on integers? *)
    match op with
    | APlusA -> "+"
    | AMinusA -> "-"
    | AMult -> "*"
    | ADiv -> "/"
    | AMod -> "%"
    | AEq -> "=="
    | ANe -> "!="
    | ALOr -> "or"
    | ALAnd -> "and"
    | ABAnd -> "&"
    | ABOr -> "|"
    | ABXor -> "^"
    | AShiftlt -> "<<"
    | AShiftrt -> ">>"
    | ALt -> "<"
    | AGt -> ">"
    | AGe -> ">="
    | ALe -> "<="
  in

  Format.fprintf out.fmt "(";
  pp_arm_term out lhs;
  Format.fprintf out.fmt " %s " infix;
  pp_arm_term out rhs;
  Format.fprintf out.fmt ")"

and pp_arm_term (out : contract_printer) (term : arm_term) =
  match term.node with
  | AConst logical -> pp_arm_logical_constant out logical
  | ABinOp (op, lhs, rhs) -> pp_arm_binop out op lhs rhs
  | ALval host -> pp_arm_lvalue out host
  | ACast (_is_implicit_conversion, _convert_to_type, term) ->
      (*TODO cast correctly*)
      pp_arm_term out term
  | SP -> Format.fprintf out.fmt "SP"
(*| _ ->
      (*Format.fprintf out.fmt "<<<<";
      Printer.pp_term out.fmt term;
      Format.fprintf out.fmt
        ">>>>"*)
      raise (ArmException "Unknown pp_arm_term")*)

let pp_no_overflow (out : contract_printer) (o : no_overflow_type)
    (lhs : arm_term) (rhs : arm_term) =
  let prefix =
    match o with
    | Osub -> "BVSubNoOverflow"
    | Oadd -> "BVAddNoOverflow"
    | Omul -> "BVMulNoOverflow"
    | Odiv -> "BVSDivNoOverflow"
  in

  let suffix = match o with Osub | Oadd | Omul -> ", True" | Odiv -> "" in
  Format.fprintf out.fmt "%s(" prefix;
  pp_arm_term out lhs;
  Format.fprintf out.fmt ", ";
  pp_arm_term out rhs;
  Format.fprintf out.fmt "%s)" suffix

let rec pp_arm_predicate (out : contract_printer) (predicate : arm_predicate) =
  let fmt = out.fmt in
  match predicate with
  | Aunknown -> Format.fprintf fmt "FreshBool()"
  | Aiff (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " == ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aif (c, t1, t2) ->
      Format.fprintf fmt "If(";
      pp_arm_term out c;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t2;
      Format.fprintf fmt ")"
  (*| Aoverflow (o, lhs, rhs) -> pp_no_overflow out o lhs rhs*)
  | Afalse -> Format.fprintf fmt "False"
  | Atrue -> Format.fprintf fmt "True"
  | Aand (p1, p2) ->
      Format.fprintf fmt "And(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aor (p1, p2) ->
      Format.fprintf fmt "Or(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aimplies (p1, p2) ->
      Format.fprintf fmt "Implies(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Axor (p1, p2) ->
      Format.fprintf fmt "Xor(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Arel (rel, t1, t2) ->
      (* TODO unsigned *)
      let cmp =
        match rel with
        | Rlt -> "<"
        | Rge -> ">="
        | Rle -> "<="
        | Rgt -> ">"
        | Rneq -> "!="
        | Req -> "=="
      in
      pp_arm_term out t1;
      Format.fprintf fmt " %s " cmp;
      pp_arm_term out t2
  | _ -> raise (ArmException "Unknown pp_arm_predicate")

let add_variable (term : arm_term) (name : arm_logic_var)
    (predicate : arm_predicate) =
  Aand
    ( predicate,
      Arel (Req, node_to_term term.ty (Translation.var_to_arm name), term) )

let add_variables (variables : (arm_logic_var * arm_term) list)
    (predicate : arm_predicate) =
  List.fold_left
    (fun p (name, term) -> add_variable term name p)
    predicate variables

let print_contract (out : Format.formatter) (contract : arm_contract) =
  let (formatter : contract_printer) = { fmt = out } in

  Format.fprintf out "\n# Old Variables\n";
  List.iter
    (fun (name, _) -> Format.fprintf out "%s = Int('%s')\n" name name)
    contract.enviroment.old;

  Format.fprintf out "\n# Pre State\n";
  Format.fprintf out "REG = Array('REG(s)', IntSort(), IntSort())\n";
  Format.fprintf out "MEM = Array('MEM(s)', IntSort(), IntSort())\n";
  Format.fprintf out "\n# Pre Contract\n";

  Format.fprintf out "OldVar = ";
  pp_arm_predicate formatter
    (add_variables contract.enviroment.old Atrue |> simplify);
  Format.fprintf out "\n";

  Format.fprintf out "Requires = ";
  pp_arm_predicate formatter contract.requires;
  Format.fprintf out "\n";

  Format.fprintf out "\n# Post State\n";
  Format.fprintf out "REG = Array('REG(s\\')', IntSort(), IntSort())\n";
  Format.fprintf out "MEM = Array('MEM(s\\')', IntSort(), IntSort())\n";

  Format.fprintf out "\n# Post Contract\n";

  Format.fprintf out "Ensures = ";
  pp_arm_predicate formatter contract.ensures;
  Format.fprintf out "\n";

  (* OldVar is included as it binds the variables *)
  Format.fprintf out "\n# Bindings\n";
  Format.fprintf out "P = And(OldVar, Requires)\n";
  Format.fprintf out "R = Ensures\n";
  Format.fprintf out "\n"

let print_arm_overflow (out : Format.formatter) (fn : fundec) =
  let (formatter : contract_printer) = { fmt = out } in
  let contract = fn_to_arm fn in

  (* Check if the contract implies is equal to itself, aka if overflow affects the result *)
  let check =
    Aiff
      ( Aand (contract.requires, contract.ensures),
        Aand (contract.requires, contract.ensures) )
  in
  pp_arm_predicate formatter check
