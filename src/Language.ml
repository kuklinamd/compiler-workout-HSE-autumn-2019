(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
      
      primary:
        n:DECIMAL {Const n}
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let read (state, input, o) var =
      match input with
        | i :: ins -> (State.update var i state, ins, o)
        | _ -> failwith "Nothing to read from the input."

    let write (s, i, output) value = (s, i, output @ [value])

    let assign (state, i, o) var value = (State.update var value state, i, o)

    let rec eval env (state, ins, outs) as config = function
      | Read   var              -> read config var
      | Write  expr             -> write config (Expr.eval state expr)
      | Assign (var, expr)      -> assign config var (Expr.eval state expr)
      | Seq    (stmt1, stmt2)   -> eval env (eval env config stmt1) stmt2
      | Skip                    -> config
      | If     (cond, thn, els) -> eval env config (if Expr.eval state cond != 0 then thn else els)

      | While  (cond, body) as stmt ->
        if Expr.eval state cond != 0
        then eval env (eval env config body) stmt
        else config

      | Repeat (body, cond) as stmt ->
        let (state, _, _) as config = eval env config body in
        if Expr.eval state cond == 0
        then eval env config stmt
        else config

      | Call   (name, exprs) ->
        let (args, locals, body) = env#definition name               in
        let state' = State.push_scope state (args @ locals)          in
        let exprs  = List.map (fun arg -> Expr.eval state arg) exprs in
        let map    = List.combine args exprs                         in
        let state' = List.fold_left (fun st (arg, expr) -> State.update arg expr st) state' map  in
        let (state'', ins, outs) = eval env (state', ins, outs) body in
        (State.drop_scope state'' state, ins, outs)

    (* Statement parser *)
    ostap (
      parse: stmts; (*empty {failwith "Not implemented yet"}*)

      expr: !(Expr.parse);

      special_elif:
        -"elif" e:expr -"then" thn:stmts els:special_elif {If (e, thn, els)}
      | -"else" s:stmts -"fi"                             {s}
      | -"fi"                                             {Skip}
      ;

      special_if:
        -"if" e:expr -"then" thn:stmts els:special_elif   {If (e, thn, els)}
      ;

      listByDot:
        <x::xs> : !(Util.listBy)[ostap(",")][expr] {x::xs}
        | empty                                    {[]}
        ;

      stmt:
          x:IDENT -":=" e:expr                 {Assign (x, e)}
        | name:IDENT -"(" args:listByDot -")"  {Call (name, args)}
        | -"write" -"(" e:expr -")"            {Write e}
        | -"read" -"(" x:IDENT -")"            {Read x}
        | -"while" e:expr
          -"do" body:stmts -"od"               {While (e, body)}
        | -"skip"                              {Skip}
        | -"repeat" body:stmts
          -"until" e:expr                      {Repeat (body, e)}
        | -"for" s1:stmt -"," e:expr "," s2:stmt
          -"do" s3:stmts -"od"                 {Seq (s1, While (e, Seq (s3, s2)))}
        | special_if
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
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
