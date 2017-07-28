(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

type out_type =
  | Lem_ast_out
  | Lem_out of string option
  | Ocaml_out of string option

let get_lexbuf f =
  let in_chan = open_in f in
  let lexbuf = Lexing.from_channel in_chan in
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = f;
                                Lexing.pos_lnum = 1;
                                Lexing.pos_bol = 0;
                                Lexing.pos_cnum = 0; };
  lexbuf, in_chan

let parse_file (f : string) : Parse_ast.defs =
  let scanbuf, in_chan = get_lexbuf f in
  let type_names =
    try
      Pre_parser.file Pre_lexer.token scanbuf
    with
      | Parsing.Parse_error ->
          let pos = Lexing.lexeme_start_p scanbuf in
           raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "pre")))
      | Parse_ast.Parse_error_locn(l,m) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, m)))
      | Lexer.LexError(s,p) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, s))) in
  let () = Lexer.custom_type_names := !Lexer.custom_type_names @ type_names in
  close_in in_chan;
  let lexbuf, in_chan = get_lexbuf f in
    try
      let ast = Parser.file Lexer.token lexbuf in
      close_in in_chan; ast
    with
      | Parsing.Parse_error ->
          let pos = Lexing.lexeme_start_p lexbuf in
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "main")))
      | Parse_ast.Parse_error_locn(l,m) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, m)))
      | Lexer.LexError(s,p) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, s)))

let convert_ast (order : Ast.order) (defs : Parse_ast.defs) : unit Ast.defs = Initial_check.process_ast order defs

let load_file_no_check order f = convert_ast order (parse_file f)

let load_file order env f =
  let ast = convert_ast order (parse_file f) in
  Type_check.check env ast

let opt_new_typecheck = ref false
let opt_just_check = ref false
let opt_ddump_tc_ast = ref false
let opt_dno_cast = ref false

let check_ast (defs : unit Ast.defs) : Type_check.tannot Ast.defs * Type_check.Env.t =
  let ienv = if !opt_dno_cast then Type_check.Env.no_casts Type_check.initial_env else Type_check.initial_env in
  let ast, env = Type_check.check ienv defs in
  let () = if !opt_ddump_tc_ast then Pretty_print.pp_defs stdout ast else () in
  let () = if !opt_just_check then exit 0 else () in
  (ast, env)

let monomorphise_ast locs ast =
  let ast = Monomorphise.split_defs locs ast in
  let ienv = Type_check.Env.no_casts Type_check.initial_env in
  Type_check.check ienv ast

let rewrite_ast (defs: Type_check.tannot Ast.defs) = Rewriter.rewrite_defs defs
let rewrite_ast_lem (defs: Type_check.tannot Ast.defs) = Rewriter.rewrite_defs_lem defs
let rewrite_ast_ocaml (defs: Type_check.tannot Ast.defs) = Rewriter.rewrite_defs_ocaml defs

let open_output_with_check file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  (o', (o, temp_file_name, file_name))

let open_output_with_check_unformatted file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  (o, temp_file_name, file_name)

let always_replace_files = ref true

let close_output_with_check (o, temp_file_name, file_name) =
  let _ = close_out o in
  let do_replace = !always_replace_files || (not (Util.same_content_files temp_file_name file_name)) in
  let _ = if (not do_replace) then Sys.remove temp_file_name
          else Util.move_file temp_file_name file_name in
  ()

let generated_line f =
  Printf.sprintf "Generated by Sail from %s." f

let output1 libpath out_arg filename defs  =
  let f' = Filename.basename (Filename.chop_extension filename) in
    match out_arg with
      | Lem_ast_out ->
	begin
	  let (o, ext_o) = open_output_with_check (f' ^ ".lem") in
	  Format.fprintf o "(* %s *)@\n" (generated_line filename);
          Format.fprintf o "open import Interp_ast@\n";
	  Format.fprintf o "open import Pervasives@\n";
          Format.fprintf o "(*Supply common numeric constants at the right type to alleviate repeated calls to typeclass macro*)\n";
          Format.fprintf o "let zero  : integer = integerFromNat 0\n";
          Format.fprintf o "let one   : integer = integerFromNat 1\n";
          Format.fprintf o "let two   : integer = integerFromNat 2\n";
          Format.fprintf o "let three : integer = integerFromNat 3\n";
          Format.fprintf o "let four  : integer = integerFromNat 4\n";
          Format.fprintf o "let five  : integer = integerFromNat 5\n";
          Format.fprintf o "let six   : integer = integerFromNat 6\n";
          Format.fprintf o "let seven : integer = integerFromNat 7\n";
          Format.fprintf o "let eight : integer = integerFromNat 8\n";
          Format.fprintf o "let fifteen : integer = integerFromNat 15\n";
          Format.fprintf o "let sixteen : integer = integerFromNat 16\n";
          Format.fprintf o "let twenty  : integer = integerFromNat 20\n";
          Format.fprintf o "let twentythree : integer = integerFromNat 23\n";
          Format.fprintf o "let twentyfour  : integer = integerFromNat 24\n";
          Format.fprintf o "let thirty : integer = integerFromNat 30\n";
          Format.fprintf o "let thirtyone  : integer = integerFromNat 31\n";
          Format.fprintf o "let thirtytwo  : integer = integerFromNat 32\n";
          Format.fprintf o "let thirtyfive : integer = integerFromNat 35\n";
          Format.fprintf o "let thirtynine : integer = integerFromNat 39\n";
          Format.fprintf o "let forty : integer = integerFromNat 40\n";
          Format.fprintf o "let fortyseven : integer = integerFromNat 47\n";
          Format.fprintf o "let fortyeight : integer = integerFromNat 48\n";
          Format.fprintf o "let fiftyfive  : integer = integerFromNat 55\n";
          Format.fprintf o "let fiftysix   : integer = integerFromNat 56\n";
          Format.fprintf o "let fiftyseven : integer = integerFromNat 57\n";
          Format.fprintf o "let sixtyone   : integer = integerFromNat 61\n";
          Format.fprintf o "let sixtythree : integer = integerFromNat 63\n";
          Format.fprintf o "let sixtyfour  : integer = integerFromNat 64\n";
          Format.fprintf o "let onetwentyseven : integer = integerFromNat 127\n";
          Format.fprintf o "let onetwentyeight : integer = integerFromNat 128\n";
                    
          Format.fprintf o "let defs = ";
	  Pretty_print.pp_lem_defs o defs;
	  close_output_with_check ext_o
	end
      | Lem_out None ->
         let generated_line = generated_line filename in
         let types_module = (f' ^ "_embed_types") in
         let ((o,_, _) as ext_o) =
           open_output_with_check_unformatted (f' ^ "_embed_types.lem") in
         let ((o',_, _) as ext_o') =
           open_output_with_check_unformatted (f' ^ "_embed.lem") in
         let ((o'',_, _) as ext_o'') =
           open_output_with_check_unformatted (f' ^ "_embed_sequential.lem") in
	 (Pretty_print.pp_defs_lem
            (o,["Pervasives_extra";"Sail_impl_base";"Sail_values"])
            (o',["Pervasives_extra";"Sail_impl_base";"Prompt";"Sail_values";
            String.capitalize types_module])
            (o'',["Pervasives_extra";"Sail_impl_base";"State";"Sail_values";
            String.capitalize types_module])
            defs generated_line);
         close_output_with_check ext_o;
         close_output_with_check ext_o';
         close_output_with_check ext_o'';
      | Lem_out (Some lib) ->
         let generated_line = generated_line filename in
         let types_module = (f' ^ "_embed_types") in
         let ((o,_, _) as ext_o) =
           open_output_with_check_unformatted (f' ^ "_embed_types.lem") in
         let ((o',_, _) as ext_o') =
           open_output_with_check_unformatted (f' ^ "_embed.lem") in
         let ((o'',_, _) as ext_o'') =
           open_output_with_check_unformatted (f' ^ "_embed_sequential.lem") in
	 (Pretty_print.pp_defs_lem
            (o,["Pervasives_extra";"Sail_impl_base";"Sail_values"])
            (o',["Pervasives_extra";"Sail_impl_base";"Prompt";
                 "Sail_values";String.capitalize types_module;lib])
            (o'',["Pervasives_extra";"Sail_impl_base";"State";
                  "Sail_values";String.capitalize types_module;lib ^ "_sequential"])
            defs generated_line);
         close_output_with_check ext_o;
         close_output_with_check ext_o';
         close_output_with_check ext_o''
      | Ocaml_out None ->
        let ((o,temp_file_name, _) as ext_o) = open_output_with_check_unformatted (f' ^ ".ml") in
	begin Pretty_print.pp_defs_ocaml o defs (generated_line filename) ["Big_int_Z";"Sail_values"];
        close_output_with_check ext_o
        end
      | Ocaml_out (Some lib) ->
        let ((o,temp_file_name, _) as ext_o) = open_output_with_check_unformatted (f' ^ ".ml") in
	Pretty_print.pp_defs_ocaml o defs (generated_line filename) ["Big_int_Z"; "Sail_values"; lib];
        close_output_with_check ext_o

let output libpath out_arg files =
  List.iter
    (fun (f, defs) ->
       output1 libpath out_arg f defs)
    files
