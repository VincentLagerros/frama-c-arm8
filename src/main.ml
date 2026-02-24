open Cil_types (* src/kernel_services/ast_data *)

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

module Output_file = Self.String (struct
  let option_name = "-arm8-output"
  let default = "-"
  let arg_name = "output-file"
  let help = "file where the message is output (default: output to the console)"
end)

module OverflowEnabled = Self.False (struct
  let option_name = "-arm8-overflow"
  let help = "Generate the armv8 overflow check"
end)

let print_behavior (out : Format.formatter) (spec : behavior) =
  Format.fprintf out "name= [%s]\n" spec.b_name

let print_spec (out : Format.formatter) (spec : funspec) =
  Format.fprintf out " <%d> " (List.length spec.spec_behavior);
  List.iter (fun behavior -> print_behavior out behavior) spec.spec_behavior

let print_function_overflow (out : Format.formatter) (fn : fundec) =
  (* We can not access the fn.sspec directly, it will be empty *)
  let kf = Globals.Functions.get fn.svar in
  (*let sp = Annotations.funspec kf in*)

  (*Format.fprintf out "fn [%d]" (List.length (Annotations.behaviors kf));*)
  (*Format.fprintf out "/*@\n";
  List.iter (fun st -> Printer.pp_behavior out st) sp.spec_behavior;
  Format.fprintf out "\n*/@.";
  Format.fprintf out "fn ";
  Printer.pp_fundec out fn;
  Format.fprintf out "(";
  List.iter
    (fun st ->
      Printer.pp_varinfo out st;
      Format.fprintf out ",")
    fn.sformals;
  Format.fprintf out ")";

  Printer.pp_block out fn.sbody;
      *)

  let behaviors = Annotations.behaviors kf in

  Format.fprintf out "# Function %s\n" fn.svar.vname;
  Format.fprintf out "_result = BitVec(\"\\\\result\", 64)\n";
  List.iter
    (fun st ->
      Format.fprintf out "%s = BitVec(\"%s\", 64)\n" st.vorig_name st.vorig_name)
    fn.sformals;

  Format.fprintf out "check_overflow(\"%s\", " fn.svar.vname;
  Spec.print_arm_overflow out behaviors;
  Format.fprintf out ")\n";
  Format.fprintf out "@."

let print_function_regular (out : Format.formatter) (fn : fundec) =
  let kf = Globals.Functions.get fn.svar in
  let behaviors = Annotations.behaviors kf in

  Format.fprintf out "# Function %s\n" fn.svar.vname;
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
  Format.fprintf out "@."

let print_global_overflow (out : Format.formatter) = function
  | GFun (def, _location) -> print_function_overflow out def
  | _x -> Format.fprintf out ""

let print_global_regular (out : Format.formatter) = function
  | GFun (def, _location) -> print_function_regular out def
  | _x -> Format.fprintf out ""

let main (out : out_channel) =
  let fmt = Format.formatter_of_out_channel out in
  let file = Ast.get () in
  let f =
    if OverflowEnabled.get () then print_global_overflow fmt
    else print_global_regular fmt
  in
  List.iter f file.globals;
  Format.fprintf fmt "# finished@."

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
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Printf.eprintf "There was an error: %s\n" msg

let () = Boot.Main.extend run
