open Cil_types
open Specification

(*
  To do a sound translation into ARMv8 we first translate it into an intermediate representation, simplfying it in the process.
*)

let node_to_term (ty : arm_type) (node : arm_term_node) : arm_term =
  { node; ty }

let int_node_to_term = node_to_term (AInt (true, Word64))
let bool_node_to_term = node_to_term ABool

(* Inner pointer type *)
let pointer_type (ptr : arm_type) : arm_type =
  match ptr with
  | APtr x -> x
  | _ -> raise (ArmException "This type is not a pointer")

let size_of (ty : arm_type) : arm_word_size =
  match ty with
  | APtr _ -> Word64
  | AInt (_, x) -> x
  | ABool ->
      raise (ArmException "This type is a bool, and does not have a size")

let max_word (w1 : arm_word_size) (w2 : arm_word_size) : arm_word_size =
  match (w1, w2) with
  | Word64, _ | _, Word64 -> Word64
  | Word32, _ | _, Word32 -> Word32
  | Word16, _ | _, Word16 -> Word16
  | _ -> Word8

let binop_ty (ty1 : arm_type) (ty2 : arm_type) : arm_type =
  match (ty1, ty2) with
  | ABool, ABool -> ABool
  | AInt (ty1_signed, ty1_size), AInt (ty2_signed, ty2_size) ->
      (* Upcast the sign, and size *)
      AInt (ty1_signed || ty2_signed, max_word ty1_size ty2_size)
  | APtr a, APtr b ->
      if a == b then APtr a
      else raise (ArmException "Uncomparable pointer types")
  | _ -> raise (ArmException "Uncomparable types")

let int_to_arm (x : int) : arm_term =
  node_to_term (AInt (x < 0, Word64)) (AConst (AInteger (Int.to_string x)))

let var_to_arm (x : string) = ALval (AVar x)

let rec typ_to_arm (typ : typ) : arm_type =
  match typ.tnode with
  | TVoid -> raise (ArmException "Cant use void result a contract")
  | TPtr typ -> APtr (typ_to_arm typ)
  | TInt IBool | TInt IUChar -> AInt (false, Word8)
  | TInt IChar -> AInt (true, Word8)
  | TInt IUShort -> AInt (false, Word16)
  | TInt IShort -> AInt (true, Word16)
  | TInt IUInt -> AInt (false, Word32)
  | TInt IInt -> AInt (true, Word32)
  | TInt IULong | TInt IULongLong -> AInt (false, Word64)
  | TInt ILong | TInt ILongLong -> AInt (true, Word64)
  | TNamed info -> typ_to_arm info.ttype
  | TFloat _ -> raise (ArmException "Floats are not supported by L3")
  | TFun _ -> raise (ArmException "Functions are not supported")
  | _ -> raise (ArmException "Unknown typ_to_arm")

let logic_type_to_arm (logic_type : logic_type) : arm_type =
  match logic_type with
  | Ctype typ -> typ_to_arm typ
  | Lboolean -> ABool
  | Linteger -> AInt (true, Word64)
  | _ -> raise (ArmException "Unknown logic_type_to_arm")

let typ_to_size (typ : typ) = typ |> typ_to_arm |> size_of

let logic_type_to_size (logic_type : logic_type) =
  match logic_type with
  | Ctype typ -> typ_to_size typ
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown logic_type_to_size in type '%s'"
              (pp_spec Printer.pp_logic_type logic_type)))

let word_to_bytes (size : arm_word_size) : int =
  match size with Word8 -> 1 | Word16 -> 2 | Word32 -> 4 | Word64 -> 8

let logic_type_to_bytes (logic_type : logic_type) : int =
  logic_type_to_size logic_type |> word_to_bytes

let typ_to_bytes (typ : typ) : int = typ_to_size typ |> word_to_bytes

let rec term_to_arm (env : arm_enviroment) (term : term) : arm_term =
  match term.term_node with
  | TConst logical -> logical_to_arm env logical
  | TBinOp (op, lhs, rhs) -> binop_to_arm env op lhs rhs
  | TLval (host, offset) -> l_value_to_arm env host offset
  | Tat (t, label) -> at_to_arm env t label
  (* Align and sizeof is the same on ARMv8 for primative types *)
  | TSizeOf typ | TAlignOf typ -> typ_to_bytes typ |> int_to_arm
  | TAddrOf (host, offset) -> address_of_l_value env host offset
  | Tlet (x, t) -> let_term env x (fun local_env -> term_to_arm local_env t)
  (* a shortcut for (void ptr)0 *)
  | Tnull -> int_to_arm 0
  | TCast (is_implicit_conversion, convert_to_type, term) ->
      cast_to_arm env is_implicit_conversion convert_to_type term
  | Tapp _ ->
      raise
        (ArmException
           "Applications like \\max or functions like strlen are currently \
            unsupported")
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown term_to_arm %s"
              (pp_spec Printer.pp_term term)))

and address_of_l_value (_env : arm_enviroment) (lhost : term_lhost)
    (offset : term_offset) : arm_term =
  if offset != TNoOffset then raise (ArmException "Unsupported index operation")
  else
    match lhost with
    | TMem term ->
        raise
          (ArmException
             (Format.sprintf "Unknown address_of_l_value %s"
                (pp_spec Printer.pp_term term)))
        (*term_to_arm env term*)
    | _ -> raise (ArmException "Unsupported address of lvalue")

and binop_to_arm (env : arm_enviroment) (op : binop) (lhs : term) (rhs : term) :
    arm_term =
  let lhs_t = term_to_arm env lhs in
  let rhs_t = term_to_arm env rhs in

  match op with
  | Mod | Div | Mult | PlusA | MinusA | Shiftlt | Shiftrt | BAnd | BOr | BXor ->
      (* For basic ops we can just do the trivial operations *)
      let inner_op =
        match op with
        | Div -> ADiv
        | Mod -> AMod
        | Mult -> AMult
        | PlusA -> APlusA
        | MinusA -> AMinusA
        | Shiftlt -> AShiftlt
        | Shiftrt -> AShiftrt
        | BAnd -> ABAnd
        | BXor -> ABXor
        | BOr -> ABOr
        | _ ->
            raise
              (ArmException
                 "binop_to_arm inner op does not exist, this should never \
                  happend")
      in
      node_to_term
        (binop_ty lhs_t.ty rhs_t.ty)
        (ABinOp (inner_op, lhs_t, rhs_t))
  (* Adding an integer to a pointer is the equavalent of (uint64_t)lhs + rhs*size_of( *lhs ) *)
  | PlusPI | MinusPI ->
      let inner_op =
        match op with
        | PlusPI -> APlusA
        | MinusPI -> AMinusA
        | _ ->
            raise
              (ArmException
                 "binop_to_arm inner op does not exist, this should never \
                  happend")
      in

      (* Keep the outer pointer type *)
      let ty = pointer_type lhs_t.ty in
      node_to_term lhs_t.ty
        (ABinOp
           ( inner_op,
             lhs_t,
             node_to_term ty
               (ABinOp
                  (AMult, rhs_t, ty |> size_of |> word_to_bytes |> int_to_arm))
           ))
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown binary operator '%s'"
              (pp_spec Printer.pp_binop op)))

and at_to_arm (env : arm_enviroment) (term : term) (label : logic_label) :
    arm_term =
  match label with
  (* This allows old even in the "requires part", however wp will generate an error as "old undefined in this context" *)
  | BuiltinLabel Old -> env_old env term
  | _ -> raise (ArmException "Unknown label in at_to_arm")

and cast_to_arm (env : arm_enviroment) (_is_implicit_conversion : bool)
    (_convert_to_type : logic_type) (term : term) : arm_term =
  (* TODO cast correctly *)
  term_to_arm env term

and logic_var_to_arm (env : arm_enviroment) (lvar : logic_var) : arm_term =
  Hashtbl.find env.variables lvar.lv_name

(* TODO result type with signed + unsigned? *)
and l_value_to_arm (env : arm_enviroment) (lhost : term_lhost)
    (offset : term_offset) : arm_term =
  if offset != TNoOffset then raise (ArmException "Unsupported index operation")
  else
    match lhost with
    (* TODO, *&x can smuggle variables into the post-state, we need to check that we are in an \old state to do this! *)
    | TVar logical_var -> logic_var_to_arm env logical_var
    | TMem term ->
        node_to_term
          (logic_type_to_arm term.term_type)
          (ALval
             (AMemory (term_to_arm env term, logic_type_to_size term.term_type)))
    (* We can be sure this is only in a post-context as otherwise you will get "\result meaningless" error from wp *)
    | TResult typ ->
        node_to_term (typ_to_arm typ) (ALval (ARegister (0, typ_to_size typ)))

(* Puts the term into enviroment old, and returns the bound variable *)
and env_old (env : arm_enviroment) (term : term) : arm_term =
  let t = term_to_arm env term in

  (*
    We dedup on terms, so we do not fill it up with the same argument all the time, 
    as frama-c automaticlly transforms `x` to `\old(x)` if x is an argument.

    If we need perf then just make this into a hashmap
  *)
  node_to_term t.ty
    (match List.find_opt (fun (_name, term) -> term == t) env.old with
    | Some (name, _) -> var_to_arm name
    | None ->
        let length = List.length env.old in
        let name = Printf.sprintf "old_%d" length in
        env.old <- (name, t) :: env.old;
        var_to_arm name)

and logical_to_arm (_ : arm_enviroment) (logical : logic_constant) : arm_term =
  match logical with
  | Boolean b -> bool_node_to_term (AConst (ABoolean b))
  | Integer (i, _) -> int_node_to_term (AConst (AInteger (Z.to_string i)))
  | _ -> raise (ArmException "Unknown logical_to_arm")

(* TODO support -absolute-valid-range for a range of supported values instead of HOL *)
(* TODO valid range as, "ACSL built-in predicate \valid (p) is now equivalent to \validrange (p,0,0)." *)
and valid_to_arm (env : arm_enviroment) (label : logic_label) (term : term) :
    arm_predicate =
  match label with
  | StmtLabel _ -> raise (ArmException "\\valid is not supported with C labels")
  | FormalLabel _ ->
      raise (ArmException "\\valid is not supported with global annotations")
  | BuiltinLabel Here ->
      let arm_term = term_to_arm env term in

      (* The nullcheck is for "\valid{L}((char ptr)\null) and \valid_read{L}((char ptr)\null) are always false, forany logic label L"*)
      (* The mod check is for aligment for armv8, technically frama-c have the \aligned keyword, but for armv8 "safely dereferenced" means it must be aligned *)

      (*
        This is the same is HOL, but they check that the lower 3 bits are 0.

        adress bitwise-and 0b111 = 0
         ``^var_tm && 7w = 0w /\ ^prog_addr_max_tm <=+ ^var_tm /\ ^var_tm <+ ^mem_addr_bound_tm``

        where

        val prog_addr_max_tm = ``0x20000w:word64``;
        val mem_addr_bound_tm = ``0x100000000w:word64``;
      *)
      Aand
        ( Aand
            ( Arel (Rle, int_to_arm 0x20000, arm_term),
              Arel (Rlt, arm_term, int_to_arm 0x100000000) ),
          Arel
            ( Req,
              (* Keep the type*)
              node_to_term arm_term.ty
                (ABinOp
                   ( AMod,
                     arm_term,
                     int_to_arm (logic_type_to_bytes term.term_type) )),
              int_to_arm 0 ) )
  | BuiltinLabel _ ->
      raise
        (ArmException
           "\\valid is not supported with logic labels other than 'here'")

and predicate_to_arm (env : arm_enviroment) (predicate : predicate) :
    arm_predicate =
  match predicate.pred_content with
  | Pfalse -> Afalse
  | Ptrue -> Atrue
  | Piff (p1, p2) -> Aiff (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pand (p1, p2) -> Aand (predicate_to_arm env p1, predicate_to_arm env p2)
  | Por (p1, p2) -> Aor (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pimplies (p1, p2) ->
      Aimplies (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pxor (p1, p2) -> Axor (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pnot p -> Anot (predicate_to_arm env p)
  | Pif (c, p1, p2) ->
      Aif (term_to_arm env c, predicate_to_arm env p1, predicate_to_arm env p2)
  | Plet (x, p) ->
      let_predicate env x (fun local_env -> predicate_to_arm local_env p)
  | Paligned (t1, t2) ->
      Arel
        ( Req,
          node_to_term ABool
            (ABinOp (AMod, term_to_arm env t1, term_to_arm env t2)),
          int_to_arm 0 )
      (* Even if valid_read != valid, for our purposes it is equivalent as we have no restrictions on write/read *)
  | Pvalid (label, t) | Pvalid_read (label, t) -> valid_to_arm env label t
  | Prel (rel, t1, t2) ->
      Arel (rel, term_to_arm env t1, term_to_arm env t2)
      (* TODO overflow *)
      (*if options.overflow then
        Aif (Aand (no_overflow_of_term a, no_overflow_of_term b), out, Aunknown)
      else out*)
  | _ -> raise (ArmException "Unknown predicate_to_arm_predicate")

and let_predicate (env : arm_enviroment) (info : logic_info)
    (fn : arm_enviroment -> arm_predicate) : arm_predicate =
  match info.l_body with
  (* 
    Adds the let variable in the local enviroment, and then removes it. 
    Hashtbl automaticlly shadows the variable in case of duplicates 
  *)
  | LBpred predicate ->
      let arm_predicate = predicate_to_arm env predicate in
      Hashtbl.add env.predicates info.l_var_info.lv_name arm_predicate;
      let (result : 'a) = fn env in
      Hashtbl.remove env.predicates info.l_var_info.lv_name;
      result
  | LBterm term ->
      let arm_term = term_to_arm env term in
      Hashtbl.add env.variables info.l_var_info.lv_name arm_term;
      let result = fn env in
      Hashtbl.remove env.variables info.l_var_info.lv_name;
      result
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown let_predicate %s"
              (pp_spec Printer.pp_logic_info info)))

(* Generics for higher order functions are weird, so I have to duplicate it *)
and let_term (env : arm_enviroment) (info : logic_info)
    (fn : arm_enviroment -> arm_term) : arm_term =
  match info.l_body with
  | LBterm term ->
      let arm_term = term_to_arm env term in
      Hashtbl.add env.variables info.l_var_info.lv_name arm_term;
      let result = fn env in
      Hashtbl.remove env.variables info.l_var_info.lv_name;
      result
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown let_term %s"
              (pp_spec Printer.pp_logic_info info)))

(* Fold list acsl predicates into a single arm predicate using and *)
let identified_predicate_list_to_arm (env : arm_enviroment)
    (list : identified_predicate list) : arm_predicate =
  List.fold_left
    (fun acc_p item ->
      let item_p = predicate_to_arm env item.ip_content.tp_statement in
      Aand (acc_p, item_p))
    Atrue list

let behavior_to_arm (env : arm_enviroment) (fn : funbehavior) : arm_contract =
  {
    (* todo termination with termination_kind? *)
    ensures =
      identified_predicate_list_to_arm env
        (List.map (fun (_term, item) -> item) fn.b_post_cond);
    requires = identified_predicate_list_to_arm env fn.b_requires;
    enviroment = env;
  }

let varinfo_to_arm (index : int) (varinfo : varinfo) : arm_logic_var * arm_term
    =
  let size = typ_to_size varinfo.vtype in
  ( varinfo.vorig_name,
    node_to_term (typ_to_arm varinfo.vtype)
      (ALval
         (* First 8 are passed in the registers x0-x7 *)
         (if index < 8 then
            (* REG(s, i) *)
            ARegister (index, size)
          else
            (* MEM(s, SP + (i - 8), size) *)
            AMemory
              ( node_to_term
                  (AInt (false, Word64))
                  (ABinOp
                     ( APlusA,
                       node_to_term (AInt (false, Word64)) SP,
                       int_to_arm ((index - 8) * 8) )),
                size ))) )

let fn_vars_to_arm (args : varinfo list) : (arm_logic_var * arm_term) list =
  List.mapi varinfo_to_arm args

let sformals_to_env (fn : fundec) : arm_enviroment =
  let arguments = fn_vars_to_arm fn.sformals in
  let table = Hashtbl.create (List.length arguments) in
  (* All variables are substituted like "Contract-Based Verification in TriCera" *)
  List.iter (fun (key, value) -> Hashtbl.add table key value) arguments;
  { variables = table; predicates = Hashtbl.create 0; old = [] }

let fn_to_arm (fn : fundec) : arm_contract =
  let kf = Globals.Functions.get fn.svar in
  let behaviors = Annotations.behaviors kf in
  let (env : arm_enviroment) = sformals_to_env fn in

  let contract =
    List.fold_left
      (fun acc_contract item ->
        let contract = behavior_to_arm env item in
        {
          ensures = Aand (contract.ensures, acc_contract.ensures);
          requires = Aand (contract.requires, acc_contract.requires);
          enviroment = contract.enviroment;
        })
      { ensures = Atrue; requires = Atrue; enviroment = env }
      (* Wrong default beahvior for ensures? *)
      behaviors
  in
  {
    (* Simpliy away the Aand(predicate, Atrue) from folding *)
    ensures = simplify contract.ensures;
    requires = simplify contract.requires;
    enviroment = env;
  }
