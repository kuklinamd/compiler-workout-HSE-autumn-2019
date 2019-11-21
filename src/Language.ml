(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = List.init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
	let show_expr expr = show(t) expr

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
      | Const n    -> st, i, o, Some (Value.Int n)
      | Var x      -> st, i, o, Some (State.eval st x)
      | String str -> st, i, o, Some (Value.String str)

      | Binop (op, x, y) ->
        let (_, _, _, Some (Value.Int a)) = eval env conf x in
        let (s, i, o, Some (Value.Int b)) = eval env conf y in
        s, i, o, Some (Value.Int (to_func op a b))

      | Call (name, exprs) ->
        let fold_fun (c, args) e =
           let (s, i, o, Some r) = eval env c e
           in ((s, i, o, None), r :: args)
        in let (conf, args) = List.fold_left fold_fun (conf, []) exprs
        in env#definition env name (List.rev args) conf

      | Array es ->
        let rec f conf acc = function
          | [] -> (conf, acc)
          | e::es -> 
            let (_, _, _, Some r) as c = eval env conf e 
            in f c (r::acc) es
        in let (st, i, o, vs) = eval_list env conf es
        in st, i, o, Some (Value.Array vs)

      | Elem (e, ie) ->
        let (_, _, _, Some vr) as c = eval env conf e in
        let (st, i, o, Some vidx) as c' = eval env c ie in
        let idx = Value.to_int vidx in
		let el = (match vr with
          | Value.Array r -> List.nth r idx
          | Value.String s -> Value.Int (Char.code (String.get s idx)))
        in st, i, o, Some el

      | Length e ->
        let (st, i, o, Some vr) = eval env conf e in
        let len = (match vr with
          | Value.Array ar -> List.length ar
          | Value.String str -> String.length str)
        in st, i, o, Some (Value.Int len)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr
         (fun x -> x) (Array.map (fun (a, s) -> a, 
              List.map (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s)
           [|
             `Lefta, ["!!"];
             `Lefta, ["&&"];
             `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
             `Lefta, ["+" ; "-"];
             `Lefta, ["*" ; "/"; "%"];
           |]
         )
         primary_hack);

      arguments:
        <x::xs> : !(Util.listBy)[ostap(",")][parse] {x::xs}
        | empty                                     {[]}
        ;

      primary_hack:
	   expr:primary_array len:(-".length")?
       {match len with
        | None -> expr
        | Some _ -> Length expr
       };
 
      index: -"[" !(parse) -"]" ;

      primary_array:
       expr:primary elems:(index)*
       {List.fold_left (fun ar el -> Elem (ar, el)) expr elems}
	  ;

      primary:
        n:DECIMAL                           {Const n}
      | name:IDENT -"(" args:arguments -")" {Call (name, args)}
      | x:IDENT                             {Var x}
      | str:STRING                          {String (String.sub str 1 (String.length str - 2))}
      | c:CHAR                              {Const (Char.code c)}
      | -"[" els:arguments -"]"             {Array els}
      | -"(" parse -")"

    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    let show_stmts prog = show(t) prog
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> 
             Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let isSkip = function
      | Skip -> true
      | _    -> false

    let concat_cont s1 = function
      | Skip -> s1
      | s2   -> Seq (s1, s2)
          
    let rec eval env ((st, i, o, r) as conf) k = function
      | Skip          ->
        if isSkip k then conf else eval env conf Skip k

      | Assign (v, [], e) ->
        let (st, i, o, Some n) = Expr.eval env conf e in
        eval env (State.update v n st, i, o, None) Skip k

      | Assign (v, es, e) ->
        let (st, i, o, vs) = Expr.eval_list env conf es in
        let (st, i, o, Some n) = Expr.eval env conf e in
        eval env (update st v n vs, i, o, None) Skip k
       
      | Seq (s1, s2) ->
        eval env conf (concat_cont s2 k) s1

      | If (cnd, thn, els) ->
        let st, i, o, Some n = Expr.eval env conf cnd in
        if (Value.to_int n) == 0
        then eval env (st, i, o, None) k els
        else eval env (st, i, o, None) k thn

      | While (cnd, body) as whl ->
        let (st, i, o, Some n) = Expr.eval env conf cnd in
        if (Value.to_int n) == 0
        then eval env (st, i, o, None) Skip k
        else eval env (st, i, o, None) (concat_cont whl k) body

      | Repeat (body, cnd) as rpt ->
        let conf = eval env conf Skip body in
        let (st, i, o, Some n) = Expr.eval env conf cnd in
        if (Value.to_int n) == 0
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
          x:IDENT es:(-"[" expr -"]")* -":=" e:expr {Assign (x, es, e)}
        | name:IDENT -"(" args:listByComma -")"     {Call (name, args)}
        | -"while" e:expr
          -"do" body:stmts -"od"                    {While (e, body)}
        | -"skip"                                   {Skip}
        | -"repeat" body:stmts
          -"until" e:expr                           {Repeat (body, e)}
        | -"for" s1:stmt -"," e:expr "," s2:stmt
          -"do" s3:stmts -"od"                      {Seq (s1, While (e, Seq (s3, s2)))}
        | special_if
        | -"return" e:!(Expr.parse)?                {Return e}
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

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
