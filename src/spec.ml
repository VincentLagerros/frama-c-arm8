open Cil_types

exception ArmException of string

(* TODO arm term including \old, operator type ect *)

type no_overflow_type = Oadd | Osub | Omul | Odiv

type arm_predicate =
  | Afalse
  | Atrue
  | Aiff of arm_predicate * arm_predicate
  | Aif of arm_predicate * arm_predicate * arm_predicate
  | Aand of arm_predicate * arm_predicate
  | Aor of arm_predicate * arm_predicate
  | Aimplies of arm_predicate * arm_predicate
  | Anot of arm_predicate
  | Arel of relation * term * term
  | Aoverflow of no_overflow_type * term * term
  | Aunknown

type overflow = arm_predicate option

type arm_contract = {
  assumes : arm_predicate;
  ensures : arm_predicate;
  requires : arm_predicate;
}

type contract_printer = { fmt : Format.formatter }
type contract_options = { overflow : bool }

(* If we can simplify it, then do it. This is just an ad hoc solution to simplify trivial expressions intoduced in folding *)
let rec simplify (predicate : arm_predicate) : arm_predicate =
  match predicate with
  | Aand (lhs, rhs) -> (
      match (simplify lhs, simplify rhs) with
      | Atrue, Atrue -> Atrue
      | Afalse, _ | _, Afalse -> Afalse
      | Atrue, _ -> simplify rhs
      | _, Atrue -> simplify lhs
      | _, _ -> Aand (simplify lhs, simplify rhs))
  | Aor (lhs, rhs) -> (
      match (simplify lhs, simplify rhs) with
      | Afalse, Afalse -> Afalse
      | Atrue, _ | _, Atrue -> Atrue
      | Afalse, _ -> simplify rhs
      | _, Afalse -> simplify lhs
      | _, _ -> Aor (simplify lhs, simplify rhs))
  | Anot p -> (
      match simplify p with
      | Afalse -> Atrue
      | Atrue -> Afalse
      | pattern -> Anot pattern)
  | Aif (c, p1, p2) -> (
      match simplify c with
      | Atrue -> simplify p1
      | Afalse -> simplify p2
      | pattern -> Aif (pattern, simplify p1, simplify p2))
  | Aiff (lhs, rhs) -> (
      match (simplify lhs, simplify rhs) with
      | Afalse, Afalse -> Atrue
      | Atrue, Atrue -> Afalse
      | pattern_lhs, pattern_rhs -> Aiff (pattern_lhs, pattern_rhs))
  | _ -> predicate

(* Returns the predicate to check if a term contains overflow *)
let rec no_overflow_of_term (term : term) : arm_predicate =
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

(*
  
  | TLval (host, offset) -> pp_arm_lvalue out host offset
  | Tat (term, label) -> pp_arm_at out old term label
  | TCast (_is_implicit_conversion, _convert_to_type, term) 
  *)
let pp_arm_logical_constant (out : contract_printer) (constant : logic_constant)
    =
  match constant with
  | Boolean true -> Format.fprintf out.fmt "True"
  | Boolean false -> Format.fprintf out.fmt "False"
  | Integer (z, _) ->
      Format.fprintf out.fmt "%s" (Z.to_string z) (* TODO overflow *)
  | _ -> raise (ArmException "Unknown pp_arm_logical_constant")

let pp_logic_var (out : contract_printer) (var : logic_var) =
  Format.fprintf out.fmt "%s" var.lv_name

let pp_arm_lvalue (out : contract_printer) (host : term_lhost)
    (_offset : term_offset) =
  match host with
  | TResult _ -> Format.fprintf out.fmt "_result"
  | TVar v -> pp_logic_var out v
  (* TODO more *)
  | _ -> raise (ArmException "Unknown pp_arm_lvalue")

let rec pp_arm_at (out : contract_printer) (_old : bool) (term : term)
    (label : logic_label) =
  match label with
  | BuiltinLabel Old -> pp_arm_term out true term
  (* TODO more *)
  | _ -> raise (ArmException "Unknown pp_arm_at")

and pp_arm_binop (out : contract_printer) (old : bool) (op : binop) (lhs : term)
    (rhs : term) : unit =
  let infix =
    match op with
    | PlusA -> " + "
    | MinusA -> " - "
    | Mult -> " * "
    | Div -> " / "
    | _ -> raise (ArmException "Unknown pp_arm_binop")
  in
  pp_arm_term out old lhs;
  Format.fprintf out.fmt "%s" infix;
  pp_arm_term out old rhs

and pp_arm_term (out : contract_printer) (old : bool) (term : term) =
  match term.term_node with
  | TConst logical -> pp_arm_logical_constant out logical
  | TBinOp (op, lhs, rhs) -> pp_arm_binop out old op lhs rhs
  | TLval (host, offset) -> pp_arm_lvalue out host offset
  | Tat (term, label) -> pp_arm_at out old term label
  | TCast (_is_implicit_conversion, _convert_to_type, term) ->
      (*TODO cast correctly*)
      pp_arm_term out old term
  | _ ->
      (*Format.fprintf out.fmt "<<<<";
      Printer.pp_term out.fmt term;
      Format.fprintf out.fmt
        ">>>>"*)
      raise (ArmException "Unknown pp_arm_term")

let pp_no_overflow (out : contract_printer) (o : no_overflow_type) (lhs : term)
    (rhs : term) =
  let prefix =
    match o with
    | Osub -> "BVSubNoOverflow"
    | Oadd -> "BVAddNoOverflow"
    | Omul -> "BVMulNoOverflow"
    | Odiv -> "BVSDivNoOverflow"
  in

  let suffix = match o with Osub | Oadd | Omul -> ", True" | Odiv -> "" in
  Format.fprintf out.fmt "%s(" prefix;
  pp_arm_term out false lhs;
  Format.fprintf out.fmt ", ";
  pp_arm_term out false rhs;
  Format.fprintf out.fmt "%s)" suffix

let rec pp_arm_predicate (out : contract_printer) (predicate : arm_predicate) =
  let fmt = out.fmt in
  match predicate with
  | Aunknown -> Format.fprintf fmt "FreshBool()"
  | Aiff (lhs, rhs) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out lhs;
      Format.fprintf fmt " == ";
      pp_arm_predicate out rhs;
      Format.fprintf fmt ")"
  | Aif (condition, t1, t2) ->
      Format.fprintf fmt "If(";
      pp_arm_predicate out condition;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t2;
      Format.fprintf fmt ")"
  | Aoverflow (o, lhs, rhs) -> pp_no_overflow out o lhs rhs
  | Afalse -> Format.fprintf fmt "False"
  | Atrue -> Format.fprintf fmt "True"
  | Aand (a, b) ->
      Format.fprintf fmt "And(";
      pp_arm_predicate out a;
      Format.fprintf fmt ", ";
      pp_arm_predicate out b;
      Format.fprintf fmt ")"
  | Aor (a, b) ->
      Format.fprintf fmt "Or(";
      pp_arm_predicate out a;
      Format.fprintf fmt ", ";
      pp_arm_predicate out b;
      Format.fprintf fmt ")"
  | Aimplies (a, b) ->
      Format.fprintf fmt "Implies";
      pp_arm_predicate out a;
      Format.fprintf fmt ", ";
      pp_arm_predicate out b;
      Format.fprintf fmt ")"
  | Arel (rel, a, b) ->
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
      pp_arm_term out false a;
      Format.fprintf fmt "%s" cmp;
      pp_arm_term out false b
  | _ -> raise (ArmException "Unknown pp_arm_predicate")

(* TODO arm terms in some way *)
let rec predicate_to_arm_predicate (options : contract_options)
    (predicate : predicate) : arm_predicate =
  match predicate.pred_content with
  | Pfalse -> Afalse
  | Ptrue -> Atrue
  | Piff (a, b) ->
      Aiff
        ( predicate_to_arm_predicate options a,
          predicate_to_arm_predicate options b )
  | Pand (a, b) ->
      Aand
        ( predicate_to_arm_predicate options a,
          predicate_to_arm_predicate options b )
  | Por (a, b) ->
      Aor
        ( predicate_to_arm_predicate options a,
          predicate_to_arm_predicate options b )
  | Prel (rel, a, b) ->
      let out = Arel (rel, a, b) in
      if options.overflow then
        Aif (Aand (no_overflow_of_term a, no_overflow_of_term b), out, Aunknown)
      else out
  | _ -> raise (ArmException "Unknown predicate_to_arm_predicate")

(* Fold list acsl predicates into a single arm predicate using and *)
let identified_predicate_list_to_arm (options : contract_options)
    (list : identified_predicate list) : arm_predicate =
  List.fold_left
    (fun acc_p item ->
      let item_p =
        predicate_to_arm_predicate options item.ip_content.tp_statement
      in
      Aand (acc_p, item_p))
    Atrue list

let behavior_to_arm (options : contract_options) (fn : funbehavior) :
    arm_contract =
  {
    assumes = identified_predicate_list_to_arm options fn.b_assumes;
    (* todo termination with termination_kind? *)
    ensures =
      identified_predicate_list_to_arm options
        (List.map (fun (_term, item) -> item) fn.b_post_cond);
    requires = identified_predicate_list_to_arm options fn.b_requires;
  }

let behavior_list_to_arm (options : contract_options) (list : funbehavior list)
    : arm_contract =
  let contract =
    List.fold_left
      (fun acc_contract item ->
        let contract = behavior_to_arm options item in
        {
          assumes = Aand (contract.assumes, acc_contract.assumes);
          ensures = Aand (contract.ensures, acc_contract.ensures);
          requires = Aand (contract.requires, acc_contract.requires);
        })
      { assumes = Atrue; ensures = Atrue; requires = Atrue }
      list
  in
  {
    (* Simpliy away the Aand(predicate, Atrue) from folding *)
    assumes = simplify contract.requires;
    ensures = simplify contract.ensures;
    requires = simplify contract.requires;
  }

let print_arm_overflow (out : Format.formatter) (behaviors : funbehavior list) =
  let formatter : contract_printer = { fmt = out } in
  let contract = behavior_list_to_arm { overflow = true } behaviors in

  (* Check if the contract implies is equal to itself, aka if overflow affects the result *)
  let check =
    Aiff
      ( Aand (contract.requires, contract.ensures),
        Aand (contract.requires, contract.ensures) )
  in
  pp_arm_predicate formatter check
