(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

module Big_int = Nat_big_num

type ('a, 'b) infix_token =
  | Primary of 'a
  | Operator of 'b
  | Chain of 'b list
  | Prefix of 'b

let map_infix_token_id f = function
  | Primary t -> Primary t
  | Operator op -> Operator (f op)
  | Chain ops -> Chain (List.map f ops)
  | Prefix p -> Prefix (f p)

let is_unary = function
  | Prefix _ -> true
  | _ -> false
              
module type Config =
  sig
    type primary
    type id
    type l
    type ctx

    val primary_loc : primary -> l

    val id_loc : id -> l
       
    val get_precedence : ctx -> id -> Big_int.num

    val left_associative : ctx -> id -> bool

    val non_associative : ctx -> id -> bool

    val chains : id -> id -> bool

    val error : l -> string -> exn
  end
 
module Make(C: Config) = struct

  let parse ctx tokens =
    let output = Queue.create () in
    let operators = Stack.create () in

    let the_chain = function
      | Operator o -> [o]
      | Chain ops -> ops
      | _ -> assert false in
 
    let rec go = function
      | [] -> ()
      | token :: tokens ->
         begin match token with
         | Primary x ->
            Queue.add (Primary x) output
         | (Operator o1 | Prefix o1) as operator1 ->
            let prec1 = C.get_precedence ctx o1 in
            let chain = ref [] in
            let rec pop_ops () = match Stack.top_opt operators with
              | Some ((Operator o2 | Chain (o2 :: _) | Prefix o2) as operator2) ->
                 let prec2 = C.get_precedence ctx o2 in
                 if Big_int.greater prec2 prec1 || (Big_int.equal prec2 prec1 && C.left_associative ctx o1) then (
                   Queue.add (Stack.pop operators) output;
                   pop_ops ()
                 ) else if C.chains o2 o1 then (
                   chain := the_chain (Stack.pop operators)
                 ) else if Big_int.equal prec2 prec1 && (C.non_associative ctx o1 || C.non_associative ctx o2) then (
                   raise (C.error (C.id_loc o1) "Ambiguous operator precedence")
                 )
              | _ -> () in
            pop_ops ();
            begin match !chain with
            | [] ->
               Stack.push operator1 operators
            | chain ->
               Stack.push (Chain (o1 :: chain)) operators
            end
         | Chain _ ->
            assert false
         end;
         go tokens
    in
    go tokens;
    
    let rec pop_remaining () =
      match Stack.pop_opt operators with
      | Some op ->
         Queue.add op output;
         pop_remaining ()
      | None -> () in
    pop_remaining();

    List.of_seq (Queue.to_seq output)

  let tree ~f ~prefix ~operator ~chain rpn =
    let values = Stack.create () in

    let rec popn = function
      | 0 -> []
      | n ->
         let vs = popn (n - 1) in
         let v = Stack.pop values in
         (v :: vs) in
    
    let rec go = function
      | first :: rest ->
         begin match first with
         | Primary value ->
            Stack.push (f value) values
         | Prefix p ->
            let arg = Stack.pop values in
            Stack.push (prefix p arg) values
         | Operator op ->
            let rhs = Stack.pop values in
            let lhs = Stack.pop values in
            Stack.push (operator op lhs rhs) values
         | Chain ops ->
            let args = popn (List.length ops + 1) in
            Stack.push (chain ops args) values
         end;
         go rest
      | [] -> ()
    in
    go rpn;

    Stack.pop values
    
end
