(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)

    let toBool x =
      match x with
        | 0 -> false
        | _ -> true

    let toInt b = if b then 1 else 0

    let matchOp op =
      match op with
        | "+" -> (+)
        | "-" -> (-)
        | "*" -> ( * )
        | "/" -> ( / )
        | "%" -> (mod)
        | "<" ->  (fun x y -> toInt (x <  y))
        | ">" ->  (fun x y -> toInt (x >  y))
        | "<=" -> (fun x y -> toInt (x <= y))
        | ">=" -> (fun x y -> toInt (x >= y))
        | "==" -> (fun x y -> toInt (x =  y))
        | "!=" -> (fun x y -> toInt (x <> y))
        | "&&" -> (fun x y -> toInt ((toBool x) && (toBool y)))
        | "!!" -> (fun x y -> toInt ((toBool x) || (toBool y)))
        | x -> failwith @@ Printf.sprintf "Unsupported operation: %s" x


    let rec eval state expr =
      match expr with
        | Const i -> i
        | Var   x -> state x
        | Binop (op, expr1, expr2) -> matchOp op (eval state expr1) (eval state expr2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
        parse: expr; (*empty {failwith "Not implemented yet"}*)

        expr:
            !(Util.expr
                (fun x -> x)
                [|
                    `Lefta, [ostap("!!"), (fun x y -> Binop ("!!", x, y))];

                    `Lefta, [ostap("&&"), (fun x y -> Binop ("&&", x, y))];

                    `Nona,   [ostap("=="), (fun x y -> Binop ("==", x, y));
                              ostap("!="), (fun x y -> Binop ("!=", x, y));
                              ostap("<="), (fun x y -> Binop ("<=", x, y));
                              ostap("<"),  (fun x y -> Binop ("<", x, y));
                              ostap(">="), (fun x y -> Binop (">=", x, y));
                              ostap(">"),  (fun x y -> Binop (">", x, y))];

                    `Lefta,  [ostap("+"), (fun x y -> Binop ("+", x, y));
                              ostap("-"), (fun x y -> Binop ("-", x, y))];

                    `Lefta, [ostap("*"), (fun x y -> Binop ("*", x, y));
                              ostap("%"), (fun x y -> Binop ("%", x, y));
                              ostap("/"), (fun x y -> Binop ("/", x, y))];

                |]
                primary
            );
        primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")"
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    let extract_state (state, _, _) = state

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    (*  let eval _ = failwith "Not implemented yet" *)

    let read (state, input, output) var =
      match input with
        | i :: ins -> (Expr.update var i state, ins, output)
        | _ -> failwith "Nothing to read from the input."

    let write (state, input, output) value = (state, input, output @ [value])

    let assign (state, input, output) var value = (Expr.update var value state, input, output)

    let rec eval config stmt =
      let state = extract_state config in
      match stmt with
        | Read var           -> read config var
        | Write expr         -> write config (Expr.eval state expr)
        | Assign (var, expr) -> assign config var (Expr.eval state expr)
        | Seq (stmt1, stmt2) -> eval (eval config stmt1) stmt2


    (* Statement parser *)
    ostap (
      parse: stmts; (*empty {failwith "Not implemented yet"}*)

      expr: !(Expr.parse);

      stmt:
          x:IDENT -":=" e:expr    {Assign (x, e)}
        | -"write" -"(" e:expr -")" {Write e}
        | -"read" -"(" x:IDENT -")" {Read x};

      stmts:
        <s::ss> : !(Util.listBy)[ostap(";")][stmt] {
            List.fold_left (fun s ss -> Seq (s, ss)) s ss
        }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
