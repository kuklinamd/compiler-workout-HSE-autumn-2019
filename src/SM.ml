open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let show_prog prg = List.fold_right (fun i acc -> Printf.sprintf "%s\n%s" (show(insn) i) acc) prg ""
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        

let binop (cs, stack, c) op =
  match stack with
  | y :: x :: stack' -> 
   let x = Value.to_int x in
   let y = Value.to_int y in
   cs, Value.Int (Expr.to_func op x y) :: stack', c
  | _ -> failwith "Unable to apply binary operation: too few elements in the stack."

let const (cs, stack, c) x = (cs, Value.Int x :: stack, c)

let load (cs, stack, (state, i, o)) v = 
  cs, (State.eval state v) :: stack, (state, i, o)

let store (cs, stack, (state, i, o)) v =
  match stack with
    | s :: stack' -> (cs, stack', (State.update v s state, i, o))
    | _ -> failwith "Unable to store a value: empty stack."

let storea (cs, stack, (state, i, o)) vl idx =
  match stack with
   | s :: stack' -> 
      let is, stack'' = split idx stack' in
      let st = Stmt.update state vl s (List.rev is) in 
      cs, stack'', (st, i, o)
   | _ -> failwith "Unable to store an array: empty stack."

let sstring (cs, stack, conf) s = (cs, Value.String s :: stack, conf)

let eval_inst config = function
  | BINOP op   -> binop config op
  | CONST x    -> const config x
  | LD    v    -> load config v
  | ST    v    -> store config v
  | STA (v, i) -> storea config v i
  | STRING s   -> sstring config s

let match_cond = function
  | "nz" -> (fun z -> z != 0)
  | "z"  -> (fun z -> z == 0)

let rec match_args args stack =
  match args, stack with
  | a :: args, s :: stack ->
    let stack', m = match_args args stack in
    stack', (a, s) :: m
  | [], stack -> stack, []
  | _  -> failwith ":c"

let call (cs, st, (state, i, o)) p = ((p, state) :: cs, st, (state, i, o))

let rec eval env ((cstack, stack, ((st, i, o) as c)) as config) = function
  | []              -> config
  | instr :: instrs ->
    match instr with
    | LABEL _            -> 
      eval env config instrs
    | JMP label          -> 
      eval env config (env#labeled label)
    | CJMP (cond, label) ->
      let z :: stack = stack in
      if match_cond cond (Value.to_int z)
      then eval env (cstack, stack, c) (env#labeled label)
      else eval env (cstack, stack, c) instrs

    | CALL (name, n, p) ->
      if env#is_label name
      then eval env (call config instrs) (env#labeled name)
      else eval env (env#builtin config name n p) instrs

    | BEGIN (name, args, lcls) ->
      let st'       = State.enter st (args @ lcls) in
      let stack', m = match_args args stack in
      let st'       = List.fold_left (fun st' (a, s) -> State.update a s st') st' m
      in eval env (cstack, stack', (st', i, o)) instrs
	
    | RET _ | END ->
      (match cstack with
       | []                -> config
       | (p, st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) p)

    | _ -> eval env (eval_inst config instr) instrs


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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

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

let gen_end_label state = function
  | true -> 
    let label, state' = state#next_end_label
    in label, state', [LABEL label]
  | _ ->
	(match state#out_label with
    | None -> let l, s = state#next_end_label in l, s, [LABEL l]
    | Some l -> l, state, [])

let rec compile_expr = function
  | Expr.Const x                  -> [CONST x]
  | Expr.Var v                    -> [LD v]
  | Expr.Binop (op, expr1, expr2) -> (compile_expr expr1) @ (compile_expr expr2) @ [BINOP op]

  | Expr.Call (name, exprs)       ->
    List.fold_left (fun acc expr -> compile_expr expr @ acc)
    [CALL (name, List.length exprs, false)]
    exprs
  | Expr.String str -> [STRING str]
  | Expr.Length arr -> 
    compile_expr arr @ [CALL ("$length", 1, false)]
  | Expr.Elem (arr, idx) ->
    let a = compile_expr arr in
    let ids = compile_expr idx in
    a @ ids @ [CALL ("$elem", 2, false)] 
  | Expr.Array arr ->
   let e = List.fold_right (fun expr acc -> compile_expr expr @ acc) arr []
   in e @ [CALL ("$array", List.length e, false)]

let rec compile_stmt state has_next_op = function
  | Stmt.Skip              -> state, []

  | Stmt.Assign (v, [], e) -> state, compile_expr e @ [ST v]
  | Stmt.Assign (v, es, e) -> 
    let es' = List.fold_right (fun expr acc -> compile_expr expr @ acc) es []
    in let e' =  compile_expr e
    in state, es' @ e' @ [STA (v, List.length es)]

  | Stmt.Seq (stmt1, stmt2) ->
        let state, instr1 = compile_stmt state true  stmt1 in
        let state, instr2 = compile_stmt state false stmt2 in
    state, instr1 @ instr2

  | Stmt.If (cnd, thn, els) ->
    let label_end, state, foot = gen_end_label state has_next_op in
    let label_else, state = state#next_label in
    let state, instr_thn  = compile_stmt state false thn in
    let state, instr_els  = compile_stmt state false els in
    let state = state#reset_out in

    state, compile_expr cnd         @
           [CJMP ("z", label_else)] @
           instr_thn                @
           [JMP label_end;
            LABEL label_else]       @
           instr_els                @
           foot

  | Stmt.While (cnd, body)  ->
    let label_start, state = state#next_label in
    let label_end,   state = state#next_label in
    let state, body = compile_stmt state false body in
    state, [LABEL label_start]     @
            compile_expr cnd       @
           [CJMP ("z", label_end)] @
            body                   @
           [JMP label_start;
            LABEL label_end]
  | Stmt.Repeat (body, cnd) ->
    let label_start, state = state#next_label in
    let state, body = compile_stmt state false body in
        state, [LABEL label_start] @
            body               @
            compile_expr cnd   @
           [CJMP ("z", label_start)]

  | Stmt.Call (name, exprs) ->
    state, List.fold_left (fun acc expr -> compile_expr expr @ acc)
           [CALL (name, List.length exprs, true)]
           exprs
  | Stmt.Return None     -> state, [RET false]
  | Stmt.Return (Some n) -> state, compile_expr n @ [RET true]

let compile_def cst (name, (args, locals, body)) =
  let cst, stmts = compile_stmt cst false body in
  cst,  [LABEL name;
         BEGIN (name, args, locals)] @
         stmts                 @
        [END]

let compile_defs cst defs = 
  let f (cst, acc) def =
      let cst', def = compile_def cst def
      in cst', def @ acc
  in List.fold_left f (cst, []) defs

let compile (defs, p) =
  let cst = new compile_state in
  let cst, defs = compile_defs cst defs in
  let body = snd @@ compile_stmt cst false p
 in body @ [END] @ defs
