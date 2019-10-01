open GT       
open Language
       
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         

let matchOp = Language.Expr.matchOp

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
    | s :: stack' -> (stack', (Language.Expr.update v s state, i, o))
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

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)

let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]

(* Mine *)
(* 
let rec compile_expr expr =
  match expr with
    | Language.Expr.Const x -> [CONST x]
    | Language.Expr.Var v -> [LD v]
    | Language.Expr.Binop (op, expr1, expr2) -> compile_expr expr1 @ compile_expr expr2 @ [BINOP op]

let rec compile stmt =
  match stmt with
    | Language.Stmt.Read v             -> [READ; ST v]
    | Language.Stmt.Write expr         -> compile_expr expr @ [WRITE]
    | Language.Stmt.Assign (v, expr)   -> compile_expr expr @ [ST v]
    | Language.Stmt.Seq (stmt1, stmt2) -> compile stmt1 @ compile stmt2
*)
