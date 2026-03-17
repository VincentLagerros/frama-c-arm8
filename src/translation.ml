open Cil_types
open Specification

(*
  To do a sound translation into ARMv8 we first translate it into an intermediate representation, simplfying it in the process.
*)

let int_to_arm (x : int) : arm_term = AConst (AInteger (Int.to_string x))
let var_to_arm (x : string) = ALval (AVar x)

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
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown logic_type_to_size in type '%s'"
              (pp_spec Printer.pp_logic_type logic_type)))

let word_to_bytes (size : arm_word_size) : int =
  match size with Word8 -> 1 | Word16 -> 2 | Word32 -> 4 | Word64 -> 8

let logic_type_to_bytes (logic_type : logic_type) : int =
  logic_type_to_size logic_type |> word_to_bytes

let typ_to_bytes (typ : typ) : int = type_to_size typ |> word_to_bytes

let rec term_to_arm (env : arm_enviroment) (term : term) : arm_term =
  match term.term_node with
  | TConst logical -> AConst (logical_to_arm env logical)
  | TBinOp (op, lhs, rhs) ->
      ABinOp (op, term_to_arm env lhs, term_to_arm env rhs)
  | TLval (host, offset) -> l_value_to_arm env host offset
  | Tat (term, label) -> at_to_arm env term label
  | TSizeOf typ -> typ_to_bytes typ |> int_to_arm
  (*| Tlet (logical_info, term) ->
      TODO let binding with logical info, also for let predicates, from looking at it let is more used in predicates

      Hashtbl.add env.variables logical_info.l_var_info.lv_name (linfo_to_arm logical_info);
      term_to_arm env term
      *)
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
    | TVar logical_var -> logic_var_to_arm env logical_var
    | TMem term ->
        ALval
          (AMemory (term_to_arm env term, logic_type_to_size term.term_type))
    (* We can be sure this is only in a post-context as otherwise you will get "\result meaningless" error from wp *)
    | TResult typ -> ALval (ARegister (0, type_to_size typ))
(*

      match offset with
      | TNoOffset -> term
      | TIndex(_index_term, _index_offset) ->
        raise (ArmException "test1")
          (*ALval
            (AMemory (term_to_arm env term, logic_type_to_size term.term_type))*)
      | _ -> raise (ArmException "test"))

in
  let (offset : arm_term_offset) =
    match offset with
    | TNoOffset -> ANoOffset
    | TIndex (term, TNoOffset) -> AIndex (term_to_arm env term, ANoOffset)
    | _ -> raise (ArmException "Unknown l_value_to_arm offset")
  in
  ALval new_host*)

(* Puts the term into enviroment old, and returns the bound variable *)
and env_old (env : arm_enviroment) (term : term) : arm_term =
  let t = term_to_arm env term in

  (*
    We dedup on terms, so we do not fill it up with the same argument all the time, 
    as frama-c automaticlly transforms `x` to `\old(x)` if x is an argument.

    If we need perf then just make this into a hashmap
  *)
  match List.find_opt (fun (_name, term) -> term == t) env.old with
  | Some (name, _) -> var_to_arm name
  | None ->
      let length = List.length env.old in
      let name = Printf.sprintf "old_%d" length in
      env.old <- (name, t) :: env.old;
      var_to_arm name

and logical_to_arm (_ : arm_enviroment) (logical : logic_constant) :
    arm_logic_constant =
  match logical with
  | Boolean b -> ABoolean b
  | Integer (i, _) -> AInteger (Z.to_string i)
  | _ -> raise (ArmException "Unknown logical_to_arm")

(* TODO support -absolute-valid-range for a range of supported values instead of HOL *)
(* TODO valid range as, "ACSL built-in predicate \valid (p) is now equivalent to \validrange (p,0,0)." *)
let valid_to_arm (env : arm_enviroment) (label : logic_label) (term : term) :
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

let varinfo_to_arm (index : int) (varinfo : varinfo) : arm_logic_var * arm_term
    =
  let size = type_to_size varinfo.vtype in
  ( varinfo.vorig_name,
    ALval
      (if index <= 7 then
         (* REG(s, i) *)
         ARegister (index, size)
       else
         (* MEM(s, SP + (i - 8), size) *)
         AMemory (ABinOp (PlusPI, SP, int_to_arm (index - 8)), size)) )

let fn_vars_to_arm (args : varinfo list) : (arm_logic_var * arm_term) list =
  List.mapi varinfo_to_arm args

let sformals_to_env (fn : fundec) : arm_enviroment =
  let arguments = fn_vars_to_arm fn.sformals in
  let table = Hashtbl.create (List.length arguments) in
  (* All variables are substituted like "Contract-Based Verification in TriCera" *)
  List.iter (fun (key, value) -> Hashtbl.add table key value) arguments;
  { variables = table; old = [] }

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
