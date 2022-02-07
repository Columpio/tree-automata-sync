module tree_automata_sync.Program
open System

module Example =
    let private aname = IdentGenerator.gensymp "a"
    let private var n = Var (IdentGenerator.gensymp n)
    let private a, x, y = Var aname, var "x", var "y"
    let private c1, c2, d1, d2 = var "cl", var "cr", var "dl", var "dr"
    let private L = Apply(IdentGenerator.gensymp "L", [])
    let binaryConstructor c = let c = IdentGenerator.gensymp c in fun (x, y) -> Apply(c, [x; y])
    let private N = binaryConstructor "N"
    let private af = binaryConstructor "af"
    let private cf = binaryConstructor "cf"
    let private df = binaryConstructor "df"
    let unaryConstructor c = let c = IdentGenerator.gensymp c in fun x -> Apply(c, [x])
    let private S = unaryConstructor "S"
    let private af1 = unaryConstructor "af1"

    let pattern2a pattern = AutomatonApply("A", pattern)
    let pattern2b pattern = AutomatonApply("B", pattern |> Pattern.freeVars |> Set.toList |> List.map Var |> Pattern)

    module Example1 =
        let pattern = Pattern [a; N(x, y)]
        let instantiator = Map.ofList [ aname, cf(c1, c2) ]

    module Example2 =
        let pattern = Pattern [a; N(L, N(x, y))]
        let instantiator = Map.ofList [ aname, af(cf(c1, c2), df(d1, d2)) ]

    module Example3 =
        let pattern = Pattern [a; N(L, N(x, y))]
        let instantiator = Map.ofList [ aname, af(c1, df(d1, d2)) ]

    module Example4 =
        let pattern = Pattern [a; S(x)]
        let instantiator = Map.ofList [ aname, af1(y) ]

let printQuery A B =
    printfn "Хотим:"
    printfn $"""{B} \in Fb <=> {A} \in Fa"""
    printfn ""

let printInstance instantiator A B =
    let A' = State.instantiate instantiator A
    let B' = State.instantiate instantiator B
    printfn "Инстанцируем:"
    printfn $"""{B'} \in Fb <=>"""
    printfn $"""  Fa \ni {A'} ="""
    let A'' = State.unfoldAutomatonApply A'
    printfn $"\t {A''}"
    printfn ""
    A'', B'

let printFinal A B =
    printfn "Положим:"
    let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
    let abstrVars = abstrVarsMap |> Map.toList |> List.map fst
    let freeConstrs = State.freeConstructors abstrState
    let freeConstrsStr = freeConstrs |> List.map toString |> join ", "
    printfn $"""Fb := {{ (({freeConstrsStr}), ({abstrVars |> List.map toString |> join ", "})) |{"\n\t"}{abstrState} \in Fa }}"""
    printfn ""
    printfn "Тогда инвариант:"
    let inv = Invariant(freeConstrs, List.map (Map.findOrApply SVar abstrVarsMap) abstrVars)
    printfn $"""{B} = {inv}"""
    printfn ""
    inv

let printInduction B invariantA =
    let freeVars = State.freeVars B |> Set.toList
    let N = max (State.maxFunctionArity B) (Invariant.maxFunctionArity invariantA)
    let instantiator=
        freeVars
        |> List.map (fun ident -> ident, Term.mkApplyNary N ident (fun _ -> Term.mkFreshVar ()))
        |> Map.ofList
    printfn "Индукционная раскрутка слева:"
    let B' = State.instantiate instantiator B
    printfn $"{B'} ="
    let B'' = State.unfoldAutomatonApply B'
    printfn $"\t{B''} ="
    let sideB = Invariant.rewrite B'' (B, invariantA)
    printfn $"\t{sideB}"
    printfn ""

    let invariantA' = Invariant.instantiate instantiator invariantA
    let invariantA'' = Invariant.unfoldAutomatonApply invariantA'
    printfn "Индукционная раскрутка справа:"
    printfn $"{invariantA'} ="
    printfn $"\t{invariantA''}"
    printfn ""

    sideB, invariantA''

let printInductionSchema leftSide rightSide =
    printfn "Соединение левой и правой части:"
    printfn $"{leftSide} =\n\t{rightSide}\n"

    let callsLeft = State.collectAutomatonApplies leftSide
    let callsRight = Invariant.collectAutomatonApplies rightSide
    let callsDiff = Set.difference callsRight callsLeft
    if Set.isEmpty callsDiff then
        let abstrLeftSide, (_, state2vars) = State.abstractAutomatonApplies leftSide
        let abstrRightSide =
            let mapper name pat =
                let a = AutomatonApply(name, pat)
                match Map.tryFind a state2vars with
                | Some ident -> SVar ident
                | None -> a
            Invariant.mapAutomatonApplies mapper rightSide
        printfn "Итоговая индукционная схема:"
        printfn $"{abstrLeftSide} =\n{abstrRightSide}"
    else
        printfn "Что из правой части не хватает в левой:"
        callsDiff |> Set.toList |> List.map toString |> join ", " |> sprintf "Количество: %d, Состояния: %s." (Set.count callsDiff) |> printfn "%s"

[<EntryPoint>]
let main _ =
    Console.OutputEncoding <- System.Text.Encoding.UTF8

    let pattern = Example.Example4.pattern
    let instantiator = Example.Example4.instantiator

    let A = Example.pattern2a pattern
    let B = Example.pattern2b pattern
    printQuery A B
    let A, B = printInstance instantiator A B
    let invariantA = printFinal A B
    let leftSide, rightSide = printInduction B invariantA
    printInductionSchema leftSide rightSide
    0
