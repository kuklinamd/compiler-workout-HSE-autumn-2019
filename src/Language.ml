(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)
    

    let rec eval env ((st, i, o, r) as conf) = function
      | Const n          -> (st, i, o, Some n)
      | Var   x          -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y) ->
        let (_, _, _, Some a) = eval env conf x in
        let (s, i, o, Some b) = eval env conf y in
        (s, i, o, Some (to_func op a b)) 
      | Call (name, exprs) -> 
        let fold_fun (c, args) e =
           let (s, i, o, Some r) = eval env c e
           in ((s, i, o, None), r :: args)
        in let (conf, args) = List.fold_left fold_fun (conf, []) exprs
        in env#definition env name (List.rev args) conf

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
    *)

    ostap (
      parse:
      !(Ostap.Util.expr 
             (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
        `Lefta, ["!!"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
              |] 
         )
         primary);
      
      arguments:
        <x::xs> : !(Util.listBy)[ostap(",")][parse] {x::xs}
        | empty                                    {[]}
        ;

      primary:
        n:DECIMAL {Const n}
      | name:IDENT -"(" args:arguments -")" {Call (name, args)}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )

    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)


    let isSkip = function 
      | Skip -> true
      | _    -> false

    let concat_cont s1 = function
      | Skip -> s1
      | s2   -> Seq (s1, s2)

    let rec eval env ((st, i, o, r) as conf) k = function
      | Skip          ->
        if isSkip k then conf else eval env conf Skip k

      | Assign (v, e) ->
        let (st, i, o, Some n) = Expr.eval env conf e in
        eval env (State.update v n st, i, o, None) Skip k

      | Write e ->
        let (st, i, o, Some n) = Expr.eval env conf e in
        eval env (st, i, o @ [n], None) Skip k 

      | Read v ->
        eval env (State.update v (List.hd i) st, List.tl i, o, None) Skip k

      | Seq (s1, s2) ->
        eval env conf (concat_cont s2 k) s1

      | If (cnd, thn, els) ->
        let (st, i, o, Some n) = Expr.eval env conf cnd in
        if n == 0
        then eval env (st, i, o, None) k els
        else eval env (st, i, o, None) k thn

      | While (cnd, body) as whl ->
        let (st, i, o, Some n) = Expr.eval env conf cnd in
        if n == 0
        then eval env (st, i, o, None) Skip k
        else eval env (st, i, o, None) (concat_cont whl k) body

      | Repeat (body, cnd) as rpt ->
        let conf = eval env conf Skip body in
        let (st, i, o, Some n) = Expr.eval env conf cnd in
        if n == 0
        then eval env (st, i, o, None) k rpt
        else eval env (st, i, o, None) Skip k
        
      | Call (name, exprs) ->
        let fold_fun (c, args) e =
           let (s', i', o', Some r) = Expr.eval env c e
           in ((s', i', o', None), r :: args)
        in let (conf, args) = List.fold_left fold_fun (conf, []) exprs
        in eval env (env#definition env name (List.rev args) conf) Skip k

      | Return (Some expr) -> Expr.eval env conf expr
      | Return _ -> conf
        
 
    (* Statement parser *)
    ostap (
      parse: stmts;

      expr: !(Expr.parse);

      special_elif:
        -"elif" e:expr -"then" thn:stmts els:special_elif {If (e, thn, els)}
      | -"else" s:stmts -"fi"                             {s}
      | -"fi"                                             {Skip}
      ;

      special_if:
        -"if" e:expr -"then" thn:stmts els:special_elif   {If (e, thn, els)}
      ;

      listByComma:
        <x::xs> : !(Util.listBy)[ostap(",")][expr] {x::xs}
        | empty                                    {[]}
        ;

      stmt:
          x:IDENT -":=" e:expr                  {Assign (x, e)}
        | name:IDENT -"(" args:listByComma -")" {Call (name, args)}
        | -"write" -"(" e:expr -")"             {Write e}
        | -"read" -"(" x:IDENT -")"             {Read x}
        | -"while" e:expr
          -"do" body:stmts -"od"                {While (e, body)}
        | -"skip"                               {Skip}
        | -"repeat" body:stmts
          -"until" e:expr                       {Repeat (body, e)}
        | -"for" s1:stmt -"," e:expr "," s2:stmt
          -"do" s3:stmts -"od"                  {Seq (s1, While (e, Seq (s3, s2)))}
        | special_if
        | -"return" e:!(Expr.parse)?            {Return e}
        ;

      stmts:
        <s::ss> : !(Util.listBy)[ostap(";")][stmt] {
            List.fold_left (fun s ss -> Seq (s, ss)) s ss
        }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    let from_option n = function
      | None   -> n
      | Some n -> n

    ostap (
      parse: func;

      name: n:IDENT {n};

      listByComma:
        <x::xs> : !(Util.listBy)[ostap(",")][name] {x::xs}
        | empty                                    {[]};

      func: 
          -"fun" n:IDENT -"(" args:listByComma -")"
          lcs:(-"local" listByComma)?
          -"{" body:!(Stmt.parse) -"}"             {(n, (args, from_option [] lcs, body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)

let isSeq = function
  | Stmt.Seq _ -> "true"
  | _ -> "false"

let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
