open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let s_top (z :: stack, c) = z, (stack, c)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
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

    
let match_cond = function
  | "nz" -> (fun z -> z != 0) 
  | "z"  -> (fun z -> z == 0) 

let rec eval env config prog =
  match prog with
    | [] -> config
    | inst :: insts ->
      match inst with
        | LABEL _            -> eval env config insts
        | JMP label          -> eval env config (env#labeled label)
        | CJMP (cond, label) ->
          let z, config = s_top config in
          if match_cond cond z
          then eval env config (env#labeled label)
          else eval env config insts
        | _ -> eval env (eval_inst config inst) insts

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)

let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let rec compile_expr = function
  | Expr.Const x                  -> [CONST x]
  | Expr.Var v                    -> [LD v]
  | Expr.Binop (op, expr1, expr2) -> (compile_expr expr1) @ (compile_expr expr2) @ [BINOP op]

let is_none = function
  | None -> true
  | _    -> false

let get_some = function
  | Some x -> x

class compile_state =
  object (self)
	val num = 0
 	val _out_label = None

    method out_label = _out_label 

    method reset_out = {< _out_label = None >}

    method next_label = "label_" ^ (string_of_int num), {< num = num + 1 >}

    method next_end_label =
     let label = "label_" ^ (string_of_int num)
     in label, {< num = num + 1; _out_label = Some label >}
  end

let gen_end_label state has_next_op =
  if has_next_op
  then
    (* After the statement we have some operations so we can't make 
     * a long jump out and need to generate a new label. *)
    let label, state' = state#next_end_label
    in label, state', [LABEL label]
  else 
   (* Here we know that there's no other operation after the statement
      and we can either generate a new label or jump to the outter one.
    *)
    if is_none state#out_label
    then
      (* If there's no other label just generate a new one. *)
      let l, s = state#next_end_label
      in l, s, [LABEL l]
    else
      let label = get_some state#out_label
      in label, state, [] (*[JMP label]*)

let rec compile_stmt state has_next_op = function
  (* Simple operations. *)
  | Stmt.Read v             -> state, [READ; ST v]
  | Stmt.Write expr         -> state, compile_expr expr @ [WRITE]
  | Stmt.Assign (v, expr)   -> state, compile_expr expr @ [ST v]
  | Stmt.Skip               -> state, []

  (* Sequence: for stmt1 we know that it has following operation. *)
  | Stmt.Seq (stmt1, stmt2) ->
	let state, instr1 = compile_stmt state true  stmt1 in
	let state, instr2 = compile_stmt state false stmt2 in
    state, instr1 @ instr2

  (* If `if` statement has a next operation we nevertheless need
   * to generate a new label.
   *)
  | Stmt.If (cnd, thn, els) ->

    let label_end, state, foot = gen_end_label state has_next_op in

	let label_else, state = state#next_label in

    let state, instr_thn  = compile_stmt state false thn in
    let state, instr_els  = compile_stmt state false els in
    let state = state#reset_out in

    state, compile_expr cnd @
           [CJMP ("z", label_else)] @
           instr_thn @
           [JMP label_end;
            LABEL label_else] @
           instr_els @
		   foot

  | Stmt.While (cnd, body)  ->
    let label_start, state = state#next_label in
    let label_end,   state = state#next_label in
    let state, body = compile_stmt state false body in
    state, [LABEL label_start] @
            compile_expr cnd @
           [CJMP ("z", label_end)] @
            body @ 
           [JMP label_start;
            LABEL label_end]

let compile stmt = snd @@ compile_stmt (new compile_state) false stmt
