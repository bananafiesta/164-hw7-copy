open Ast

exception Stuck of expr

let () =
  Printexc.register_printer (function
    | Stuck e ->
        Some (Printf.sprintf "Stuck[%s]" (string_of_expr e))
    | _ ->
        None)
