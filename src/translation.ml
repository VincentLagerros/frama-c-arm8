open Cil_types
open Specification

(*
  To do a sound translation into ARMv8 we first translate it into an intermediate representation, simplfying it in the process.
*)

let int_to_arm (x : int) : arm_term = AConst (AInteger (Int.to_string x))
let var_to_arm (x : string) = ALval (AVar x, ANoOffset)

let rec type_to_size (typ : typ) =
  match typ.tnode with
  | TVoid -> raise (ArmException "Cant use void result a contract")
  | TInt IBool | TInt IChar | TInt IUChar -> Word8
  | TInt IShort | TInt IUShort -> Word16
  | TInt IInt | TInt IUInt -> Word32
  | TInt ILong | TInt IULong | TInt ILongLong | TInt IULongLong | TPtr _ ->
      Word64
  | TNamed info -> type_to_size info.ttype
  | TFloat _ -> raise (ArmException "Floats are not supported by L3")
  | TFun _ -> raise (ArmException "Functions are not supported")
  | _ -> raise (ArmException "Unknown env_result")

let logic_type_to_size (logic_type : logic_type) =
  match logic_type with
  | Ctype typ -> type_to_size typ
  | _ -> raise (ArmException "Unknown logic_type_to_size")

let word_to_bytes (size : arm_word_size) : int =
  match size with Word8 -> 1 | Word16 -> 2 | Word32 -> 4 | Word64 -> 8

let logic_type_to_bytes (logic_type : logic_type) : int =
  logic_type_to_size logic_type |> word_to_bytes

let typ_to_bytes (typ : typ) : int = type_to_size typ |> word_to_bytes

(* TODO let bindings, can be solved with free variables or replacement, not sure which is better *)
let rec term_to_arm (env : arm_enviroment) (term : term) : arm_term =
  match term.term_node with
  | TConst logical -> AConst (logical_to_arm env logical)
  | TBinOp (op, lhs, rhs) ->
      ABinOp (op, term_to_arm env lhs, term_to_arm env rhs)
  | TLval (host, offset) -> l_value_to_arm env host offset
  | Tat (term, label) -> at_to_arm env term label
  | TSizeOf typ -> typ_to_bytes typ |> int_to_arm
  (* a shortcut for (void ptr)0 *)
  | Tnull -> int_to_arm 0
  | TCast (is_implicit_conversion, convert_to_type, term) ->
      cast_to_arm env is_implicit_conversion convert_to_type term
  | _ ->
      (*Format.fprintf out.fmt "<<<<";
      Printer.pp_term out.fmt term;
      Format.fprintf out.fmt
        ">>>>"*)
      raise (ArmException "Unknown pp_arm_term")

and at_to_arm (env : arm_enviroment) (term : term) (label : logic_label) :
    arm_term =
  match label with
  (* This allows old even in the "requires part", however wp will generate an error as "old undefined in this context" *)
  | BuiltinLabel Old -> env_old env term
  | _ -> raise (ArmException "Unknown label in at_to_arm")

and cast_to_arm (env : arm_enviroment) (_is_implicit_conversion : bool)
    (_convert_to_type : logic_type) (term : term) : arm_term =
  (*TODO cast correctly*)
  term_to_arm env term

(* TODO result type with signed + unsigned? *)
and l_value_to_arm (env : arm_enviroment) (lhost : term_lhost)
    (offset : term_offset) : arm_term =
  let (new_host : arm_term_lhost) =
    match lhost with
    | TVar logical_var -> AVar logical_var.lv_name
    | TMem term ->
        AMemory (term_to_arm env term, logic_type_to_size term.term_type)
    (* We can be sure this is only in a post-context as otherwise you will get "\result meaningless" error from wp *)
    | TResult typ -> ARegister (0, type_to_size typ)
  in
  let (offset : arm_term_offset) =
    match offset with
    | TNoOffset -> ANoOffset
    | TIndex (term, TNoOffset) -> AIndex (term_to_arm env term, ANoOffset)
    | _ -> raise (ArmException "Unknown l_value_to_arm offset")
  in
  ALval (new_host, offset)

(* Puts the term into enviroment old, and returns the bound variable *)
and env_old (env : arm_enviroment) (term : term) : arm_term =
  let t = term_to_arm env term in
  let length = List.length env.old in
  let name = Printf.sprintf "old_%d" length in
  env.old <- (t, name) :: env.old;
  ALval (AVar name, ANoOffset)

and logical_to_arm (_ : arm_enviroment) (logical : logic_constant) :
    arm_logic_constant =
  match logical with
  | Boolean b -> ABoolean b
  | Integer (i, _) -> AInteger (Z.to_string i)
  | _ -> raise (ArmException "Unknown logical_to_arm")

(* TODO support -absolute-valid-range for a range of supported values instead of p!=0*)
(* TODO valid range as, "ACSL built-in predicate \valid (p) is now equivalent to \validrange (p,0,0)." *)
let valid_to_arm (env : arm_enviroment) (label : logic_label) (term : term) :
    arm_predicate =
  match label with
  | StmtLabel _ -> raise (ArmException "\\valid is not supported with C labels")
  | FormalLabel _ ->
      raise (ArmException "\\valid is not supported with global annotations")
  | BuiltinLabel Here ->
      let arm_term = term_to_arm env term in

      (* This is not a full semantic translation, as we assume that only null is invalid *)
      (* p != NULL && (size_t)p % size_of(p) == 0 *)

      (* The nullcheck is for "\valid{L}((char ptr)\null) and \valid_read{L}((char ptr)\null) are always false, forany logic label L"*)
      (* The mod check is for aligment for armv8, technically frama-c have the \aligned keyword, but for armv8 "safely dereferenced" means it must be aligned *)
      Aand
        ( Arel (Rneq, arm_term, int_to_arm 0),
          Arel
            ( Req,
              ABinOp
                (Mod, arm_term, int_to_arm (logic_type_to_bytes term.term_type)),
              int_to_arm 0 ) )
  | BuiltinLabel _ ->
      raise
        (ArmException
           "\\valid is not supported with logic labels other than 'here'")

let rec predicate_to_arm (env : arm_enviroment) (predicate : predicate) :
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
  | Paligned (t1, t2) ->
      Arel
        (Req, ABinOp (Mod, term_to_arm env t1, term_to_arm env t2), int_to_arm 0)
      (* Even if valid_read != valid, for our purposes it is equivalent as we have no restrictions on write/read *)
  | Pvalid (label, term) | Pvalid_read (label, term) ->
      valid_to_arm env label term
  | Prel (rel, t1, t2) ->
      Arel (rel, term_to_arm env t1, term_to_arm env t2)
      (* TODO overflow *)
      (*if options.overflow then
        Aif (Aand (no_overflow_of_term a, no_overflow_of_term b), out, Aunknown)
      else out*)
  | _ -> raise (ArmException "Unknown predicate_to_arm_predicate")

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

let varinfo_to_arm (index : int) (varinfo : varinfo) : arm_term * arm_logic_var
    =
  ( ALval
      ( (if index <= 7 then
           (* REG(s, i) *)
           ARegister (index, type_to_size varinfo.vtype)
         else
           (* MEM(s, SP + (i - 8), size) *)
           AMemory
             ( ABinOp (PlusPI, SP, int_to_arm (index - 8)),
               type_to_size varinfo.vtype )),
        ANoOffset ),
    varinfo.vorig_name )

let fn_vars_to_arm (args : varinfo list) : (arm_term * arm_logic_var) list =
  List.mapi varinfo_to_arm args

let sformals_to_env (fn : fundec) : arm_enviroment =
  { result = None; pre_variables = fn_vars_to_arm fn.sformals; old = [] }

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
