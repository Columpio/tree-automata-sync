module tree_automata_sync.Program
open System

let inline __notImplemented__() = failwith "Not implemented!"
let inline __unreachable__() = failwith "Unreachable!"
let inline toString x = x.ToString()
let inline join (s : string) (ss : string list) = String.Join(s, ss)

module List =
    let kfoldk f =
        let rec kfoldk z xs k =
            match xs with
            | [] -> k z
            | x::xs -> f z x (fun y -> kfoldk y xs k)
        kfoldk

    let mapChoose f xs =
        let rec mapChoose xs k =
            match xs with
            | [] -> k []
            | x::xs ->
                match f x with
                | Some y -> mapChoose xs (fun ys -> k (y::ys))
                | None -> None
        mapChoose xs Some

    let product xss =
        let rec product xss k =
            match xss with
            | [] -> k [[]]
            | xs::xss ->
                product xss (fun yss -> xs |> List.collect (fun x -> List.map (fun ys -> x :: ys) yss) |> k)
        product xss id

type opname = string
type ident = string
type term =
    | Var of ident
    | Apply of opname * term list
    override x.ToString() =
        match x with
        | Var i -> i
        | Apply(op, []) -> op
        | Apply(op, ts) -> $"""%s{op}(%s{ts |> List.map toString |> join ", "})"""
module Term =
    let fold z fIdent fOpname =
        let rec fold z = function
            | Var i -> fIdent i z
            | Apply(op, ts) -> List.fold fold (fOpname op z) ts
        fold z

    let map fIdent fOpname =
        let rec map = function
            | Var i -> fIdent i
            | Apply(op, ts) -> Apply(fOpname op, List.map map ts)
        map

    let mapVars f = map f id

    let freeVars = fold Set.empty Set.add (fun _ -> id)

    let Bottom = Apply("Bot", [])

    let isBottom = (=) Bottom

    let cut = function
        | Var _ -> None
        | Apply(opname, args) -> Some(opname, args)

    let private trySubstituteIdent map ident =
        match Map.tryFind ident map with
        | Some t -> t
        | None -> Var ident

    let instantiate instantiator = mapVars (trySubstituteIdent instantiator)

    let substitute constrMap varMap = map (trySubstituteIdent varMap) (fun c -> Map.tryFind c constrMap |> Option.defaultValue c)

module TermList =
    let isBottoms = List.forall Term.isBottom

    let freeVars = List.map Term.freeVars >> Set.unionMany

    let instantiate instantiator = List.map (Term.instantiate instantiator)

    let cutHeads = List.mapChoose Term.cut >> Option.map List.unzip

    let toString = List.map toString >> join ", "

type pattern = Pattern of term list
module Pattern =
    let fromTermList ts =
//        let ids = TermList.freeVars ts |> Set.toList
        Pattern(ts)

    let freeVars (Pattern pat) = TermList.freeVars pat

    let matchPattern (Pattern termsPat) (Pattern termsInst) =
        let rec matchWith ((constrMap, varMap) as maps) (termPat, termInst) k =
            let termPat = Term.substitute constrMap varMap termPat
            match termPat, termInst with
            | Apply(fPat, argsPat), Apply(fInst, argsInst) ->
                let maps = if fPat = fInst then maps else Map.add fPat fInst constrMap, varMap
                matchListsWith maps (List.zip argsPat argsInst) k
            | Var idPat, Var idInst ->
                if idPat = idInst then maps else constrMap, Map.add idPat termInst varMap
                |> k
            | _ -> __notImplemented__()
        and matchListsWith maps pairs k = List.kfoldk matchWith maps pairs k
        matchListsWith (Map.empty, Map.empty) (List.zip termsPat termsInst) Some

    let instantiate instantiator (Pattern(pat)) =
//        let newFreeVars used = function
//            | Choice1Of2 t ->
//                let newFree = Term.freeVars t
//                Set.difference newFree used |> Set.toList, Set.union newFree used
//            | Choice2Of2 v -> if Set.contains v used then [], used else [v], Set.add v used
//        let vars = Vars.instantiate instantiator vars |> List.mapFold newFreeVars Set.empty |> fst |> List.concat
        let pat = TermList.instantiate instantiator pat
        Pattern(pat)

    let cutHeads (Pattern pat) =
        if TermList.isBottoms pat then None else TermList.cutHeads pat

    let toString (Pattern(pat)) = TermList.toString pat

type state =
    | SVar of ident
    | CombinedState of opname list * state list // ``Delay'' states
    | AutomatonApply of ident * pattern
    | DeltaApply of ident * opname list * state list
    override x.ToString() =
        match x with
        | SVar i -> i
        | AutomatonApply(name, pat) -> $"%s{name}[%s{Pattern.toString pat}]"
        | CombinedState(constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""((%s{cs}), (%s{ss}))"""
        | DeltaApply(name, constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""delta%s{name}(%s{cs}, %s{ss})"""

module State =
    let mapPattern f =
        let rec mapPattern = function
            | SVar _ as v -> v
            | AutomatonApply(name, pattern) -> f name pattern
            | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map mapPattern states)
            | CombinedState(constrs, states) -> CombinedState(constrs, List.map mapPattern states)
        mapPattern

    let private isConstructorFree (op : string) = op.Chars(0) |> Char.IsLower //TODO

    let freeConstructors =
        let rec freeConstructors free state =
            match state with
            | DeltaApply(_, constrs, states) ->
                List.fold freeConstructors (constrs |> List.filter isConstructorFree |> Set.ofList |> Set.union free) states
            | _ -> free
        freeConstructors Set.empty >> Set.toList

    let instantiate instantiator = mapPattern (fun name pat -> AutomatonApply(name, Pattern.instantiate instantiator pat))

    let rec unfoldAutomatonApply =
        let bottomize tss =
            let N = List.map List.length tss |> List.max
            let padWithBottoms ts =
                let P = N - List.length ts
                if P = 0 then ts else
                ts @ List.init P (fun _ -> Term.Bottom)
            List.map padWithBottoms tss

        let unfoldAutomatonApply name pattern =
            match Pattern.cutHeads pattern with
            | Some(heads, bodies) ->
                let bodies = bottomize bodies
                let states = List.product bodies |> List.map (fun pat -> AutomatonApply(name, Pattern.fromTermList pat))
                let states = List.map unfoldAutomatonApply states
                DeltaApply(name, heads, states)
            | None -> AutomatonApply(name, pattern)
        mapPattern unfoldAutomatonApply

    let rec freeVars = function
        | SVar _ -> Set.empty // only vars in terms, not state vars
        | AutomatonApply(_, pattern) -> Pattern.freeVars pattern
        | DeltaApply(_, _, states) -> states |> List.map freeVars |> Set.unionMany
        | CombinedState(_, states) -> states |> List.map freeVars |> Set.unionMany

    let private matchAutomatonApplyStates statePattern stateInstance =
        match statePattern, stateInstance with
        | AutomatonApply(namePat, termsPat), AutomatonApply(nameInst, termsInst) ->
            if namePat = nameInst then Pattern.matchPattern termsPat termsInst else None
        | _ -> __unreachable__()

    let rewrite state (rewriteFromState, (rewriteToConstrs, rewriteToStates)) =
        let rec rewrite = function
            | AutomatonApply _ as a ->
                match matchAutomatonApplyStates rewriteFromState a with
                | Some substitution -> __notImplemented__()
                | None -> __notImplemented__()
            | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map rewrite states)
            | _ -> __notImplemented__()
        rewrite state

    let abstractAutomatonApplies =
        let nameFromPattern (Pattern pat) =
            pat
            |> List.map (function Var ident -> ident | Apply("Bot", []) -> "B" | _ -> __notImplemented__())
            |> join ""
            |> IdentGenerator.gensymp
        let rec abstractAutomatonApplies ((vars2states, states2vars) as maps) = function
            | SVar _ as v -> v, maps
            | AutomatonApply(_, pat) as a ->
                match Map.tryFind a states2vars with
                | Some ident -> SVar ident, maps
                | None ->
                    let freshName = nameFromPattern pat
                    SVar freshName, (Map.add freshName a vars2states, Map.add a freshName states2vars)
            | DeltaApply(name, heads, states) ->
                let states, maps = List.mapFold abstractAutomatonApplies maps states
                DeltaApply(name, heads, states), maps
            | CombinedState _ -> __unreachable__()
        abstractAutomatonApplies (Map.empty, Map.empty)

module Vars =
    let toString = List.map toString >> join ", "

    let instantiate instantiator vars =
//        vars |> List.map (fun v -> match Map.tryFind v instantiator with Some t -> Choice1Of2 t | None -> Choice2Of2 v)
        vars |> List.map (fun v -> match Map.tryFind v instantiator with Some t -> t | None -> SVar v)

module Example =
    let private aname = IdentGenerator.gensymp "a"
    let private var n = Var (IdentGenerator.gensymp n)
    let private a, x, y = Var aname, var "x", var "y"
    let private c1, c2, d1, d2 = var "cl", var "cr", var "dl", var "dr"
    let private L = Apply(IdentGenerator.gensymp "L", [])
    let binaryConstructor c (x, y) = Apply(IdentGenerator.gensymp c, [x; y])
    let private N = binaryConstructor "N"
    let private af = binaryConstructor "af"
    let private cf = binaryConstructor "cf"
    let private df = binaryConstructor "df"

    let freshVar () = Var (IdentGenerator.gensym ())

    let private pattern =
        Pattern.fromTermList [a; N(L, N(x, y))]

    let instantiator =
        [
            aname, af(cf(c1, c2), df(d1, d2))
        ] |> Map.ofList

    let A = AutomatonApply("A", pattern)
    let B = AutomatonApply("B", pattern |> Pattern.freeVars |> Set.toList |> List.map Var |> Pattern)

let printQuery A B =
    printfn "Хотим:"
    printfn $"""%O{B}\in Fb <=> %O{A} \in Fa"""
    printfn ""

let printInstance instantiator A B =
    let A' = State.instantiate instantiator A
    let B' = State.instantiate instantiator B
    printfn "Инстанцируем:"
    printfn $"""%O{B'} \in Fb <=>"""
    printfn $"""  Fa \ni %O{A'} ="""
    let A'' = State.unfoldAutomatonApply A'
    printfn $"\t %O{A''}"
    printfn ""
    A'', B'

let printFinal A B =
    printfn "Положим:"
    let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
    let abstrVars = abstrVarsMap |> Map.toList |> List.map fst
    let freeConstrs = State.freeConstructors abstrState
    let freeConstrsStr = $"""(%s{freeConstrs |> List.map toString |> join ", "})"""
    printfn $"Fb := {{ (%s{freeConstrsStr}, (%s{abstrVars |> Vars.toString})) |\n\t%O{abstrState} \in Fa }}"
    printfn ""
    printfn "Тогда инвариант:"
    let abstrValues = Vars.instantiate abstrVarsMap abstrVars
    printfn $"""%O{B} = (%s{freeConstrsStr}, (%s{abstrValues |> List.map toString |> join ", "}))"""
    freeConstrsStr, abstrValues

let printInduction B Ainvariant =
    let freeVars = State.freeVars B |> Set.toList
    let instantiator=
        freeVars
        |> List.map (fun ident -> ident, Example.binaryConstructor ident (Example.freshVar(), Example.freshVar())) //TODO: not only binary
        |> Map.ofList
    printfn "Индукционная раскрутка слева:"
    let B' = State.instantiate instantiator B
    printfn $"{B'} ="
    let B'' = State.unfoldAutomatonApply B'
    printfn $"\t{B''} ="
    let Bside = State.rewrite B'' (B, Ainvariant)
    printfn $"\t{Bside}"

    let freeConstrsStr, abstrValues = Ainvariant
    printfn "Индукционная раскрутка справа:"

[<EntryPoint>]
let main _ =
    printfn "%O" [IdentGenerator.gensym (); IdentGenerator.gensym (); IdentGenerator.gensym ()]
    printQuery Example.A Example.B
    let A, B = printInstance Example.instantiator Example.A Example.B
    let Ainvariant = printFinal A B
    printInduction B Ainvariant
    0