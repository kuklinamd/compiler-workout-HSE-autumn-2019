open GT       
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config


(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
(* let eval _ = failwith "Not yet implemented" *)

let matchOp = Syntax.Expr.matchOp

let binop (stack, c) op =
  match stack with
    | y :: x :: stack' -> ((matchOp op x y) :: stack', c)
    | _ -> failwith "Unable to apply binary operation: too few elements in the stack."
 
let const (stack, c) x = (x :: stack, c)

let read (stack, (s, input, o)) = 
  match input with
    | i :: ins -> (i :: stack, (s, ins, o))
    | _ -> failwith "Unable to read from the input: empty input."

let write (stack, (state, i, output)) =
  match stack with
    | s :: stack' -> (stack', (state, i, output @ [s]))
    | _  -> failwith "Unable to write to the output: empty stack."

let load (stack, (state, i, o)) v = ((state v) :: stack, (state, i, o))

let store (stack, (state, i, o)) v =
  match stack with
    | s :: stack' -> (stack', (Syntax.Expr.update v s state, i, o))
    | _ -> failwith "Unable to store a value: empty stack."

let eval_inst config inst = 
  match inst with
    | BINOP op -> binop config op
    | CONST x  -> const config x
    | READ     -> read config
    | WRITE    -> write config
    | LD    v  -> load config v
    | ST    v  -> store config v

let rec eval config prog =
  match prog with
    | inst :: insts -> eval (eval_inst config inst) insts
    | _ -> config

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_expr expr =
  match expr with
    | Syntax.Expr.Const x -> [CONST x]
    | Syntax.Expr.Var v -> [LD v]
    | Syntax.Expr.Binop (op, expr1, expr2) -> compile_expr expr1 @ compile_expr expr2 @ [BINOP op]

let rec compile stmt =
  match stmt with
    | Syntax.Stmt.Read v             -> [READ; ST v]
    | Syntax.Stmt.Write expr         -> compile_expr expr @ [WRITE]
    | Syntax.Stmt.Assign (v, expr)   -> compile_expr expr @ [ST v]
    | Syntax.Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2
