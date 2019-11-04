(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 4 by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

let match_cmp_op = function
   | "<"  -> "l"
   | ">"  -> "g"
   | "<=" -> "le"
   | ">=" -> "ge"
   | "==" -> "e"
   | "!=" -> "ne"

let compile_binop env op = 
  let x, y, env = env#pop2 in
  let env = env#push y in
  env, match op with
  | "+" | "-" ->
    (match x with
     | R _ ->
       [Binop (op, x, y)]
     | _   ->
       [Mov (x, eax);
        Binop (op, eax, y)])
  | "*" ->
    (match y with
     | R _ ->
       [Binop (op, x, y)]
     | _   ->
       [Mov (y, eax);
        Binop (op, x, eax);
        Mov (eax, y)]) 
  | "!!" ->
    (match x with
     | R _ ->
       [Binop ("^", edx, edx);
        Binop (op, x, y);
        Set ("nz", "%dl");
        Mov (edx, y)]
     | _   ->
       [Mov (x, eax); 
        Binop ("^", edx, edx);
        Binop (op, eax, y);
        Set ("nz", "%dl");
        Mov (edx, y)]) 
  | "&&" ->
    [Mov (x, eax);
     Binop ("cmp", L 0, eax);
     Set ("nz", "%al");
     Mov (y, edx);
     Binop ("cmp", L 0, edx);
     Set ("nz", "%dl");
     Binop ("&&", edx, eax);
     Binop ("&&", L 1, eax);
     Mov (eax, y)]
  | "/" ->
    [Mov (y, eax);
     Cltd;
     IDiv x;
     Mov (eax, y)]
  | "%" ->
    [Mov (y, eax);
     Cltd;
     IDiv x;
     Mov (edx, y)]
  | _ ->
    [Mov   (x, eax);
     Binop ("^", edx, edx);
     Binop ("cmp", eax, y);
     Set   (match_cmp_op op, "%dl");
     Mov   (edx, y)]

let compile_instr env = function
  | BINOP op -> compile_binop env op
  | CONST x ->
    let pos, env = env#allocate in
    env, [Mov (L x, pos)]
  | READ  ->
    let pos, env = env#allocate in
    env, [Call "Lread"; Mov (eax, pos)]
  | WRITE ->
    let var, env = env#pop in
    env, [Push var; Call "Lwrite"; Pop eax]
  | LD v ->
    let pos, env = env#allocate in
    env#global v, [Mov (env#loc v, eax); Mov (eax, pos)]
  | ST v ->
    let var, env = env#pop in
    env#global v, [Mov (var, eax); Mov (eax, env#loc v)]
  | LABEL label -> env, [Label label]
  | JMP label -> env, [Jmp label]
  | CJMP (cnd, lbl) ->
    let var, env = env#pop in
    env, [Mov (var, eax); Binop ("cmp", L 0, eax); CJmp (cnd, lbl)]

  | BEGIN (name, args, lcls) ->
    let env = env#enter name args lcls in
    env, [Push ebp; Mov (esp, ebp);
          Binop ("-", M ("$" ^ env#lsize), esp)]
  | END ->
    env, [Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret;
           Meta (Printf.sprintf ".set %s, %d" env#lsize (4 * env#allocated))]
  | RET true ->
    let var, env = env#pop in
    env, [Mov (var, eax); Jmp env#epilogue]

  | RET _ -> env, [Jmp env#epilogue]
  (*
	* Save registers
    * Push n values on stack
    * Call 
    * add 4 * n, esp
    * if !is_proc then push eax to symbolic stack
    * Restore registers
  *)
  | CALL (name, len, is_proc) -> 
    let handle_proc env = function
     | true -> env, []
     | false -> 
       let pos, env = env#allocate in
       env, [Mov (eax, pos)] in
    let rec push_args_on_stack env = function
      | 0 -> env, []
      | l -> 
        let v, env = env#pop in
        let env, stck = push_args_on_stack env (l - 1) in
        env, (Push v)::stck in
    let env, push_args = push_args_on_stack env len in
    let save_regs      = List.map (fun v -> Push v) env#live_registers in
    let restore_regs   = List.fold_right (fun v stck -> (Pop  v)::stck) env#live_registers [] in
    let clear_stack    = [Binop ("+", L (4 * len), esp)] in
    let env, proc      = handle_proc env is_proc in
    env, save_regs @
         (List.rev push_args) @
         [Call name] @
         clear_stack @
         proc @
         restore_regs

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env = function
 | [] -> env, []
 | instr :: prog ->
   let env, is = compile_instr env instr in
   let env, iss = compile env prog in
   env, is @ iss
                                
(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
    let rec allocate' = function
    | []                            -> ebx     , 0
    | (S n)::_                      -> S (n+1) , n+2
    | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
    | _                             -> S 0     , 1
    in
    allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
