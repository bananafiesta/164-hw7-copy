open Tokens
open Ast

exception ParseError of token list

(** [consume_token t toks] ensures that the head of [toks] is [t]. If it is, it
    returns the tail of [toks]. Otherwise, it raises a [ParseError].  *)
let consume_token : token -> token list -> token list =
  fun t toks ->
    begin match toks with
      | t' :: tail when t = t' ->
          tail

      | _ ->
          raise (ParseError toks)
    end

(** [call_or_prim f args toks] returns an expression corresponding to the
    application of [f] to [args]. If [f] is a primitive, the AST node for this
    will application will be [Prim0], [Prim1], or [Prim2]; otherwise, it will be
    [Call]. If the length of [args] does not match the arity of [f], this
    function will throw [ParseError toks]. *)
let call_or_prim : string -> expr list -> token list -> expr =
  fun f args toks ->
  begin match f with
    | "read_num" ->
        begin match args with
          | [] -> Prim0 ReadNum
          | _ -> raise (ParseError toks)
        end

    | "newline" ->
        begin match args with
          | [] -> Prim0 Newline
          | _ -> raise (ParseError toks)
        end

    | "add1" ->
        begin match args with
          | [arg] -> Prim1 (Add1, arg)
          | _ -> raise (ParseError toks)
        end

    | "sub1" ->
        begin match args with
          | [arg] -> Prim1 (Sub1, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_zero" ->
        begin match args with
          | [arg] -> Prim1 (IsZero, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_num" ->
        begin match args with
          | [arg] -> Prim1 (IsNum, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_pair" ->
        begin match args with
          | [arg] -> Prim1 (IsPair, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_empty" ->
        begin match args with
          | [arg] -> Prim1 (IsEmpty, arg)
          | _ -> raise (ParseError toks)
        end

    | "left" ->
        begin match args with
          | [arg] -> Prim1 (Left, arg)
          | _ -> raise (ParseError toks)
        end

    | "right" ->
        begin match args with
          | [arg] -> Prim1 (Right, arg)
          | _ -> raise (ParseError toks)
        end

    | "print" ->
        begin match args with
          | [arg] -> Prim1 (Print, arg)
          | _ -> raise (ParseError toks)
        end

    | "pair" ->
        begin match args with
          | [arg1; arg2] -> Prim2 (Pair, arg1, arg2)
          | _ -> raise (ParseError toks)
        end

    | _ ->
        Call (f, args)
  end

let rec parse_program : token list -> program =
  fun toks ->
    let defns, toks = parse_defns toks in
    let body, toks = parse_expr toks in
    if List.length toks <> 0 then
      raise (ParseError toks)
    else
      {defns; body}

and parse_defns : token list -> defn list * token list =
  fun toks ->
    (* let _ = print_endline "now in parse_defns" in *)
    (* ([], toks) *)
    begin match toks with
    | [] -> ([], toks)
    | FUNCTION :: rest ->
      let defn, toks2 = parse_defn rest in
      let otherdefns, toks3 = parse_defns toks2 in
      ([defn] @ otherdefns, toks3)
    | _ -> ([], toks)
    end

and parse_defn : token list -> defn * token list =
    fun toks ->
      (* let _ = print_endline "now in parse_defn" in *)
      begin match toks with
      | ID x :: LPAREN :: rest ->
        let params, rest = parse_params rest in
        (begin match rest with
        | EQ :: tail ->
          let expr, rest2 = parse_expr tail in 
          let outputdefn = {name = x; args = params; body = expr} in
          (outputdefn, rest2)
        | _ -> raise (ParseError rest)
        end
        )
        
      | _ -> raise (ParseError toks)
      end
    

and parse_params : token list -> string list * token list =
    fun toks ->
      (* let _ = print_endline "now in params" in *)
      begin match toks with
      | RPAREN :: rest ->
        ([], rest)
      | ID x :: rest ->
        let restparams, toks2 = parse_rest_params rest in 
        ([x] @ restparams, toks2)
      | _ -> raise (ParseError toks)
      end

and parse_rest_params : token list -> string list * token list =
    fun toks ->
      (* let _ = print_endline "now in rest_params" in *)
      begin match toks with
      | RPAREN :: rest ->
        ([], rest)
      | COMMA :: ID x :: rest ->
        let restparams, toks2 = parse_rest_params rest in 
        ([x] @ restparams, toks2)
      | _ -> raise (ParseError toks)
      end

and parse_expr : token list -> expr * token list =
  fun toks ->
    (* let _ = print_endline "now in expr" in *)
    begin match toks with
    | IF :: rest ->
      let expr1, tail1 = parse_expr rest in 
      (
      match tail1 with
      | THEN :: rest1 ->
        let expr2, tail2 = parse_expr rest1 in 
        (
        match tail2 with
        | ELSE :: rest2 ->
          let expr3, tail3 = parse_expr rest2 in 
          (If (expr1, expr2, expr3), tail3)
        | _ -> raise (ParseError tail2)
        )
      | _ -> raise (ParseError tail1)
      )

    | LET :: ID x :: EQ :: rest ->
      let expr1, toks1 = parse_expr rest in 
      begin match toks1 with
      | IN :: rest1 ->
        let expr2, toks2 = parse_expr rest1 in 
        (Let (x, expr1, expr2), toks2)
      | _ -> raise (ParseError toks1)
      end
    | _ -> 
      parse_seq toks
    end
    (* (True, toks) *)

and parse_seq : token list -> expr * token list =
  fun toks ->
    (* let _ = print_endline "now in seq" in *)
    let infix1, rest = parse_infix1 toks in 
    let restseq, tail = parse_rest_seq rest in 
    if ((List.length restseq) = 0)
      then (infix1, tail)
      else
        (Do ([infix1] @ restseq), tail)
    


and parse_rest_seq : token list -> expr list * token list =
  fun toks ->
    (* let _ = print_endline "now in restseq" in *)
    begin match toks with
    | [] -> 
      ([], toks)
    | SEMICOLON :: rest ->
      let infix1, tail = parse_infix1 rest in 
      let restseq, tail1 = parse_rest_seq tail in 
      ([infix1] @ restseq, tail1)
    (* | _ -> raise (ParseError toks) *)
    | _ -> ([], toks)
    end

and parse_infix1 : token list -> expr * token list =
  fun toks ->
    (* let _ = print_endline "now in infix1" in *)
    let infix2, rest = parse_infix2 toks in 
    let infix1_prime, rest1 = parse_infix1_prime rest in 
    if ((List.length infix1_prime) = 0)
      then (infix2, rest1)
      else
        let temp = List.nth infix1_prime 0 in 
        begin match temp with
        | Prim2 (prim2, _, expr2) ->
          (Prim2 (prim2, infix2, expr2), rest1)
        | _ -> raise (ParseError toks)
        end
        (* let prim2, _, expr2 = List.nth infix1_prime 0 in 
        (Prim2 (prim2, infix2, expr2), rest1) *)

and parse_infix1_prime : token list -> expr list * token list =
  fun toks ->
    (* let _ = print_endline "now in infix1'" in *)
    begin match toks with
    | [] -> ([], toks)
    | EQ :: rest ->
      let infix1, tail = parse_infix1 rest in 
      ([Prim2 (Eq, Nil, infix1)], tail)
    | LT :: rest ->
      let infix1, tail = parse_infix1 rest in 
      ([Prim2 (Lt, Nil, infix1)], tail)
    | _ -> ([], toks)
    end

and parse_infix2 : token list -> expr * token list =
  fun toks -> 
    (* let _ = print_endline "now in infix2" in *)
    let term, rest = parse_term toks in 
    let infix2_prime, rest1 = parse_infix2_prime rest in 
    if ((List.length infix2_prime) = 0)
      then (term, rest1)
      else 
        let temp = List.nth infix2_prime 0 in 
        begin match temp with
        | Prim2 (prim2, _, expr2) ->
          (Prim2 (prim2, term, expr2), rest1)
        | _ -> raise (ParseError toks)
        end
        (* let Prim2 (prim2, _, expr2) = List.nth infix2_prime 0 in 
        (Prim2 (prim2, term, expr2), rest1) *)


and parse_infix2_prime : token list -> expr list * token list =
  fun toks ->
    (* let _ = print_endline "now in infix2'" in *)
    begin match toks with
    | PLUS :: rest ->
      let infix2, tail = parse_infix2 rest in 
      ([Prim2 (Plus, Nil, infix2)], tail)
    | MINUS :: rest ->
      let infix2, tail = parse_infix2 rest in 
      ([Prim2 (Minus, Nil, infix2)], tail)
    | _ -> ([], toks)
    end

and parse_term : token list -> expr * token list =
  fun toks ->
    (* let _ = print_endline "now in term" in *)
    begin match toks with
    | ID x :: LPAREN :: rest ->
      let args, tail = parse_args rest in 
      let expr = call_or_prim x args rest in 
      (expr, tail)
    | ID x :: rest ->
      begin match x with
      | "true" ->
        (True, rest)
      | "false" ->
        (False, rest)
      | "nil" ->
        (Nil, rest)
      | _ ->
        (Var x, rest)
      end
    | NUM n :: rest ->
      (Num n, rest)
    

    | LPAREN :: rest ->
      let expr, tail = parse_expr rest in 
      begin match tail with
      | RPAREN :: tail2 ->
        (expr, tail2)

      | _ -> raise (ParseError tail)
      end
    | _ -> raise (ParseError toks)
    end

and parse_args : token list -> expr list * token list =
  fun toks ->
    (* let _ = print_endline "now in args" in *)
    begin match toks with
    | RPAREN :: rest -> 
      ([], rest)
    | _ ->
      let expr, tail = parse_expr toks in 
      let restexpr, tail2 = parse_rest_args tail in 
      ([expr] @ restexpr, tail2)
    end

and parse_rest_args : token list -> expr list * token list =
  fun toks ->
    (* let _ = print_endline "now in rest args" in *)
    begin match toks with
    | RPAREN :: rest ->
      ([], rest)
    | COMMA :: rest ->
      let expr, tail = parse_expr rest in 
      let restexpr, tail2 = parse_rest_args tail in 
      ([expr] @ restexpr, tail2)
    | _ -> raise (ParseError toks)
    end

let parse : string -> program =
  fun s ->
    s
      |> tokenize
      |> parse_program
