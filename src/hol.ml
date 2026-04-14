open Specification
open Translation
open Cil_types

type contract_printer = { fmt : Format.formatter; post : bool }
(* https://kth-step.github.io/itppv-course/ *)
(* https://github.com/kth-step/HolBA/tree/master/examples/arm8/max *)

let pp_arm_logical_constant (out : contract_printer)
    (constant : arm_logic_constant) =
  match constant with
  | ABoolean true -> Format.fprintf out.fmt "T"
  | ABoolean false -> Format.fprintf out.fmt "F"
  | AInteger z -> Format.fprintf out.fmt "%sw" z

let pp_logic_var (out : contract_printer) (var : arm_logic_var) =
  Format.fprintf out.fmt "%s" var

let rec pp_arm_lvalue (out : contract_printer) (host : arm_term_lhost) =
  match host with
  | AVar v -> pp_logic_var out v
  | ARegister (at, size) ->
      (* To simulate reading w0 or lower we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "%s.REG %dw"
            (if out.post then "ms" else "s")
            at)
  | AMemory (at, size) ->
      (* To simulate a smaller read we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "arm8_load_64 %s.MEM "
            (if out.post then "ms" else "s");
          pp_arm_term local_out at)

and pp_arm_unop (out : contract_printer) (op : arm_unop) (term : arm_term) :
    unit =
  let prefix = match op with BNot -> "~" | LNot -> "~" | Neg -> "-" in
  Format.fprintf out.fmt "%s" prefix;
  pp_arm_term out term

and pp_arm_cast_fn (out : contract_printer) (_cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size)
    (printer : contract_printer -> unit) : unit =
  let to_bits = word_to_bits to_size in
  let from_bits = word_to_bits from_size in

  if from_bits = to_bits then printer out else raise (ArmException "TODO")
(*
    let _additional_bits = to_bits - from_bits in
    (match cast with
    | AExtract ->
        Format.fprintf out.fmt "Extract(%d, 0, " (to_bits - 1)
        (* Extract is inclusive *)
    | ASignExtend -> Format.fprintf out.fmt "sign_extend("
    | AZeroExtend -> Format.fprintf out.fmt "w2w (");
    printer out;
    Format.fprintf out.fmt ")"*)

and pp_arm_cast (out : contract_printer) (cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size) (node : arm_term_node)
    : unit =
  pp_arm_cast_fn out cast to_size from_size (fun local_out ->
      pp_arm_term_node local_out node)

and pp_arm_binop (out : contract_printer) (op : arm_binop) (lhs : arm_term)
    (rhs : arm_term) : unit =
  let infix =
    match op with
    | APlusA -> "+"
    | AMinusA -> "-"
    | AMult -> "*"
    | ADiv -> "/"
    | AMod -> "mod"
    | AEq -> "="
    | ANe -> "<>"
    | ALOr -> "\\/"
    | ALAnd -> "/\\"
    | ABAnd -> "&&"
    | ABOr -> "||"
    | ABXor -> "??"
    | AShiftlt -> "<<"
    | AShiftrt -> ">>"
    | ALt | AGt | AGe | ALe -> (
        let signed = type_to_signed lhs.ty in
        if signed then
          match op with
          | ALt -> "<"
          | AGe -> ">="
          | ALe -> "<="
          | AGt -> ">"
          | _ -> raise (ArmException "Unreachable")
        else
          match op with
          | ALt -> "<+"
          | AGe -> ">=+"
          | ALe -> "<=+"
          | AGt -> ">+"
          | _ -> raise (ArmException "Unreachable"))
  in

  Format.fprintf out.fmt "(";
  pp_arm_term out lhs;
  Format.fprintf out.fmt " %s " infix;
  pp_arm_term out rhs;
  Format.fprintf out.fmt ")"

and pp_arm_term_node (out : contract_printer) (node : arm_term_node) =
  match node with
  | AConst logical -> pp_arm_logical_constant out logical
  | ABinOp (op, lhs, rhs) -> pp_arm_binop out op lhs rhs
  | ALval host -> pp_arm_lvalue out host
  | SP -> Format.fprintf out.fmt "s.SP"
  | AUnOp (op, term) -> pp_arm_unop out op term
  | ACast (cast, size, term) ->
      pp_arm_cast out cast size (size_of term.ty) term.node
  | Aif (c, t1, t2) ->
      let fmt = out.fmt in
      Format.fprintf fmt "if (";
      pp_arm_term out c;
      Format.fprintf fmt ") then (";
      pp_arm_term out t1;
      Format.fprintf fmt ") else (";
      pp_arm_term out t2;
      Format.fprintf fmt ")"

and pp_arm_term (out : contract_printer) (term : arm_term) =
  pp_arm_term_node out term.node

let rec pp_arm_predicate (out : contract_printer) (predicate : arm_predicate) =
  let fmt = out.fmt in
  match predicate with
  | Aiff (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " <=> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aif (c, t1, t2) ->
      Format.fprintf fmt "if (";
      pp_arm_term out c;
      Format.fprintf fmt ") then (";
      pp_arm_predicate out t1;
      Format.fprintf fmt ") else (";
      pp_arm_predicate out t2;
      Format.fprintf fmt ")"
  (*| Aoverflow (o, lhs, rhs) -> pp_no_overflow out o lhs rhs*)
  | Afalse -> Format.fprintf fmt "F"
  | Atrue -> Format.fprintf fmt "T"
  | Aand (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " /\\ ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aor (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " \\/ ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aimplies (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " ==> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Axor (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " <> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Arel (rel, t1, t2) ->
      let signed = type_to_signed t1.ty in

      let op =
        if signed then
          match rel with
          | Rlt -> "<"
          | Rge -> ">="
          | Rle -> "<="
          | Rgt -> ">"
          | Rneq -> "<>"
          | Req -> "="
        else
          match rel with
          | Rlt -> "<+"
          | Rge -> ">=+"
          | Rle -> "<=+"
          | Rgt -> ">+"
          | Rneq -> "<>"
          | Req -> "="
      in

      Format.fprintf fmt "(";
      pp_arm_term out t1;
      Format.fprintf fmt " %s " op;
      pp_arm_term out t2;
      Format.fprintf fmt ")"
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

let print_definition (out : Format.formatter) (fn : fundec) =
  let (fmt : contract_printer) = { fmt = out; post = false } in
  let contract = Translation.fn_to_arm fn in

  Format.fprintf out "(* -------------- *)\n";
  Format.fprintf out "(* ARMv8 contract *)\n";
  Format.fprintf out "(* -------------- *)\n";

  Format.fprintf out "\n(* ==== Function %s ====*)\n" fn.svar.vname;
  Format.fprintf out "Definition arm8_%s_pre_def:\n" fn.svar.vname;
  Format.fprintf out " arm8_%s_pre " fn.svar.vname;

  contract.enviroment.old |> List.rev
  |> List.iter (fun (name, term) ->
      Format.fprintf out "(%s:word%d) " name (term.ty |> size_of |> word_to_bits));
  Format.fprintf out "(s:arm8_state) : bool =\n  ";

  pp_arm_predicate fmt
    (add_variables contract.enviroment.old contract.requires |> simplify);

  Format.fprintf out "\nEnd\n\n";

  Format.fprintf out "Definition arm8_%s_post_def:\n" fn.svar.vname;
  Format.fprintf out " arm8_%s_post " fn.svar.vname;

  contract.enviroment.old |> List.rev
  |> List.iter (fun (name, term) ->
      Format.fprintf out "(%s:word%d) " name (term.ty |> size_of |> word_to_bits));
  Format.fprintf out "(ms:arm8_state) : bool =\n  ";

  let (fmt : contract_printer) = { fmt = out; post = true } in
  pp_arm_predicate fmt contract.ensures;

  Format.fprintf out "\nEnd";

  Format.fprintf out "\n"
