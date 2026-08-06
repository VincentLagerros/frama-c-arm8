open Cil_types (* src/kernel_services/ast_data *)
open Specification

exception IllegalArgumentException of string

let help_msg = "Simple ARMv8 translation"

module Self = Plugin.Register (struct
  let name = "ARM8"
  let shortname = "arm8"
  let help = help_msg
end)

module Enabled = Self.False (struct
  let option_name = "-arm8"
  let help = "when on (off by default), " ^ help_msg
end)

module Print_ACSL = Self.False (struct
  let option_name = "-arm8-acsl"

  let help =
    "when on (off by default), also print the Frama-C AST of the ACSL contract"
end)

module Output_file = Self.String (struct
  let option_name = "-arm8-output"
  let default = "-"
  let arg_name = "output-file"
  let help = "file where the message is output (default: output to the console)"
end)

module Output_type = Self.String (struct
  let option_name = "-arm8-type"
  let default = "hol"
  let arg_name = "output-type"
  let help = "hol|py|dbg"
end)

let print_behavior (out : Format.formatter) (spec : behavior) =
  Format.fprintf out "name= [%s]\n" spec.b_name

let print_spec (out : Format.formatter) (spec : funspec) =
  Format.fprintf out " <%d> " (List.length spec.spec_behavior);
  List.iter (fun behavior -> print_behavior out behavior) spec.spec_behavior

let print_function_dbg (out : Format.formatter)
    (source : arm_translation_source) =
  let fn = source.fn in
  let kf = Globals.Functions.get fn.svar in
  let _behaviors = Annotations.behaviors kf in

  Format.fprintf out "\n# ==== Function %s ====\n" fn.svar.vname;
  let kf = Globals.Functions.get fn.svar in
  let behaviors = Annotations.behaviors kf in
  List.iter (fun st -> Printer.pp_behavior out st) behaviors;
  Format.fprintf out "@.";

  Hol.print_definition out (Print_ACSL.get ()) source;
  Format.fprintf out "@."
(*Format.fprintf out "# Function %s\n" fn.svar.vname;
  Format.fprintf out "_result = Int(\"\\\\result\")\n";
  List.iter
    (fun st ->
      Format.fprintf out "%s = Int(\"%s\")\n" st.vorig_name st.vorig_name)
    fn.sformals;

  let formatter : Spec.contract_printer = { fmt = out } in
  let contract = Spec.behavior_list_to_arm { overflow = false } behaviors in

  Format.fprintf out "P = ";
  Spec.pp_arm_predicate formatter contract.requires;
  Format.fprintf out "\n";
  Format.fprintf out "R = ";
  Spec.pp_arm_predicate formatter contract.ensures;
  Format.fprintf out "@."*)

let print_function_py (out : Format.formatter) (source : arm_translation_source)
    =
  Py.print_definition out source;
  Format.fprintf out "@."

let print_header_py (_out : Format.formatter) (_globals : varinfo list) = ()
let print_header_dbg (_out : Format.formatter) (_globals : varinfo list) = ()

let print_header_hol (out : Format.formatter) (globals : varinfo list) =
  Hol.print_header out globals

let print_function_hol (out : Format.formatter)
    (source : arm_translation_source) =
  Hol.print_definition out (Print_ACSL.get ()) source;
  Format.fprintf out "@."

let print_ty (out : Format.formatter)
    (fn_header : Format.formatter -> varinfo list -> unit)
    (fn : Format.formatter -> arm_translation_source -> unit)
    (list : global list) =
  let global_variables = ref [] in

  (* Accumulate global variables, while not translated by the algorithm automatically it forces HOL4 to fail by letting the user define it instead *)
  List.iter
    (fun f ->
      match f with
      | GVarDecl (varinfo, _location) ->
          global_variables := varinfo :: !global_variables
      | GVar (varinfo, _initinfo, _location) ->
          (* remove GVarDecl and replace with the real definition *)
          global_variables :=
            varinfo
            :: List.filter
                 (fun var -> var.vorig_name <> varinfo.vorig_name)
                 !global_variables
      | _ -> ())
    list;

  fn_header out !global_variables;

  List.iter
    (fun f ->
      match f with
      | GFun (def, _location) ->
          fn out { fn = def; globals = !global_variables }
      | _ -> ())
    list

let main (out : out_channel) =
  let fmt = Format.formatter_of_out_channel out in
  let file = Ast.get () in

  let fn_header, fn =
    match Output_type.get () |> String.lowercase_ascii with
    | "hol" | "hol4" | "h" -> (print_header_hol, print_function_hol)
    | "py" | "python" -> (print_header_py, print_function_py)
    | "dbg" | "debug" -> (print_header_dbg, print_function_dbg)
    | _ -> raise (IllegalArgumentException "No valid output type")
  in
  print_ty fmt fn_header fn file.globals;
  Format.fprintf fmt "@."

let run () =
  try
    if Enabled.get () then (
      let filename = Output_file.get () in
      let chan =
        if Output_file.is_default () then Stdlib.stdout else open_out filename
      in
      main chan;
      flush chan;
      close_out chan)
  with
  | Specification.ArmException x ->
      Printf.eprintf "Unsupported contract: %s\n" x;
      exit 1
  | Sys_error _ as exc ->
      let msg = Printexc.to_string exc in
      Printf.eprintf "There was an error: %s\n" msg;
      exit 1

let () = Boot.Main.extend run
