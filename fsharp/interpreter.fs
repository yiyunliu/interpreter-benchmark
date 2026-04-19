module Interpreter

type Binop =
    | Add | Sub | Mul | Quotient | Le

type Expr =
    | EInt of int
    | Var of string
    | App of Expr * Expr list
    | Fix of string * string list * Expr
    | Prim of Binop * Expr * Expr
    | If of Expr * Expr * Expr

type Value =
    | VInt of int
    | VClosure of (Value list -> Value)

type Stack = {
    Data: Value []
    mutable Top: int
}

let makeStack size : Stack =
    { Data = Array.create size (VInt 0); Top = 0 }

let stackPush (stack: Stack) (v: Value) : unit =
    if stack.Top >= stack.Data.Length then failwith "stack overflow!"
    stack.Data.[stack.Top] <- v
    stack.Top <- stack.Top + 1

let stackRef (stack: Stack) (idx: int) : Value =
    stack.Data.[stack.Top - idx - 1]

let stackPop (stack: Stack) : unit =
    stack.Top <- stack.Top - 1

let applyBinop (op: Binop) (lhs: int) (rhs: int) : int =
    match op with
    | Add -> lhs + rhs
    | Sub -> lhs - rhs
    | Mul -> lhs * rhs
    | Quotient -> lhs / rhs
    | Le -> if lhs <= rhs then 1 else 0

type CEnv = CEnv of (string -> int)

let cenvEmpty : CEnv = CEnv (fun _ -> failwith "unmapped symbol")

let cenvExtend (CEnv cenv) (s: string) : CEnv =
    CEnv (fun s' -> if s' = s then 0 else 1 + cenv s')

let cenvExtendMult (cenv: CEnv) (syms: string list) : CEnv =
    List.fold cenvExtend cenv syms

let collectFree (e: Expr) : Set<string> =
    let mutable collected = Set.empty
    let rec go (bounded: Set<string>) (e: Expr) =
        match e with
        | Var s ->
            if not (Set.contains s bounded) then
                collected <- Set.add s collected
        | App (f, args) ->
            go bounded f
            List.iter (go bounded) args
        | Fix (selfName, paramNames, body) ->
            go (Set.union bounded (Set.ofList (selfName :: paramNames))) body
        | Prim (_, lhs, rhs) ->
            go bounded lhs
            go bounded rhs
        | If (g, t, e) ->
            go bounded g
            go bounded t
            go bounded e
        | EInt _ -> ()
    go Set.empty e
    collected

let collectCaptured (CEnv cenv) (e: Expr) : (string * int) list =
    let freeVars = collectFree e
    freeVars
    |> Set.toList
    |> List.map (fun var -> (var, cenv var))
    |> List.sortByDescending snd

let rec denoteFaster (cenv: CEnv) (e: Expr) : Stack -> Value =
    match e with
    | EInt n ->
        fun (_: Stack) -> VInt n
    | Var s ->
        let (CEnv cenvf) = cenv
        let dvar = cenvf s
        fun (stack: Stack) -> stackRef stack dvar
    | App (f, args) ->
        let funClos = denoteFaster cenv f
        let argCloss = List.map (denoteFaster cenv) args
        fun (stack: Stack) ->
            match funClos stack with
            | VClosure fn -> fn (List.map (fun c -> c stack) argCloss)
            | _ -> failwith "trying to apply a non-function"
    | Fix (selfName, paramNames, body) ->
        let captured = collectCaptured cenv e
        let capturedVars = List.map fst captured
        let capturedDvars = List.map snd captured
        let allParamNames = selfName :: paramNames
        let bodyClos = denoteFaster (cenvExtendMult cenv (capturedVars @ allParamNames)) body
        let len = List.length allParamNames + List.length capturedDvars
        fun (stack: Stack) ->
            let capturedArgs = capturedDvars |> List.map (stackRef stack) |> List.toArray
            let rec self (vals: Value list) =
                Array.iter (stackPush stack) capturedArgs
                List.iter (stackPush stack) (VClosure self :: vals)
                let retval = bodyClos stack
                for _ = 1 to len do stackPop stack
                retval
            VClosure self
    | Prim (op, lhs, rhs) ->
        let lhsClos = denoteFaster cenv lhs
        let rhsClos = denoteFaster cenv rhs
        fun (stack: Stack) ->
            match lhsClos stack, rhsClos stack with
            | VInt l, VInt r -> VInt (applyBinop op l r)
            | _ -> failwith "trying to apply binary arithmetic on non-numbers"
    | If (g, t, el) ->
        let guardClos = denoteFaster cenv g
        let thnClos = denoteFaster cenv t
        let elsClos = denoteFaster cenv el
        fun (stack: Stack) ->
            match guardClos stack with
            | VInt v when v = 0 -> elsClos stack
            | _ -> thnClos stack

let fib n =
    let fibExpr =
        Fix ("self", ["x"],
            If (Prim (Le, Var "x", EInt 1),
                EInt 1,
                Prim (Add,
                    App (Var "self", [Prim (Sub, Var "x", EInt 1)]),
                    App (Var "self", [Prim (Sub, Var "x", EInt 2)]))))
    let compiled = denoteFaster cenvEmpty (App (fibExpr, [EInt n]))
    let stack = makeStack 1024
    match compiled stack with
    | VInt r -> printfn "%d" r
    | VClosure _ -> printfn "<closure>"

[<EntryPoint>]
let main argv =
    match argv with
    | [| s |] -> fib (int s)
    | _ -> printfn "Usage: Interpreter <n>"
    0
