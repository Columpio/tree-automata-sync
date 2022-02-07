module test
open tree_automata_sync
open NUnit.Framework
open System

let pattern2a pattern = AutomatonApply("A", pattern)
let pattern2b pattern =
    let pattern' = pattern |> Pattern.freeVars |> Set.toList |> List.map Var                                                 // each variable one time
//    let pattern' = pattern |> Pattern.freeVarsMap |> Map.toList |> List.collect (fun (v, n) -> List.init n (fun _ -> Var v)) // each variable n times
    AutomatonApply("B", Pattern pattern')

let linearInstantiator pattern =
    let var2depth = Pattern.collectVariableDepths pattern
    let patDepth = Pattern.depth pattern
    let width = Pattern.maxFunctionArity pattern
    var2depth |> Map.map (fun _ depth -> Term.mkFullTree width (patDepth - depth))

let printQuery pattern vars2vars A B =
    let vars2vars = Map.toList vars2vars
    let origVars = vars2vars |> List.map snd |> Set.ofList |> Set.toList
    printfn $"""Хотим: L(C) = {{ ({join "," origVars}) | ({pattern}) \in L(A) }}"""
    printfn $"""Построим: {B} \in Fb <=> {A} \in Fa"""
    let newVars = match B with AutomatonApply(_, Pattern ts) -> List.map (function Var ident -> ident | _ -> __unreachable__()) ts | _ -> __unreachable__()
    printfn $"""Так что: L(C) = {{ ({join ", " origVars}) | \exists ({join ", " newVars}) \in L(B), {vars2vars |> List.map (fun (n, o) -> $"{n} = {o}") |> join ", "} }}"""
    printfn ""

let printInstance instantiator A B =
    let A' = State.instantiate instantiator A
    let B' = State.instantiate instantiator B
    printfn "Инстанцируем:"
    printfn $"""{B'} \in Fb <=>"""
    printfn $"""  Fa \ni {A'} ="""
    let A'' = State.unfoldAutomatonApplyRec A'
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
    let inv = Invariant.fromConstructorsAndStates freeConstrs (List.map (Map.findOrApply SVar abstrVarsMap) abstrVars)
    printfn $"{B} =\n\t{inv}\n"
    inv

let printInduction B invariantA =
    let freeVars = State.freeVars B |> Set.toList
    let width = max (State.maxFunctionArity B) (Invariant.maxFunctionArity invariantA)
    let instantiator=
        freeVars
        |> List.map (fun ident -> ident, Term.mkFullTree width 1)
        |> Map.ofList
    printfn "Индукционная раскрутка слева:"
    let B' = State.instantiate instantiator B
    printfn $"{B'} ="
    let B'' = State.unfoldAutomatonApplyOnce B'
    printfn $"\t{B''} ="
    let sideB = Invariant.rewrite B'' (B, invariantA)
    printfn $"\t{sideB}"
    printfn ""

    let invariantA' = Invariant.instantiate instantiator invariantA
    let invariantA'' = Invariant.unfoldAutomatonApplyRec invariantA'
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
        printfn $"{abstrLeftSide} =\n\t{abstrRightSide}"
        true
    else
        printfn "Что из правой части не хватает в левой:"
        callsDiff |> Set.toList |> List.map toString |> join ", " |> sprintf "Количество: %d, Состояния: %s." (Set.count callsDiff) |> printfn "%s"
        false

let testPattern pattern =
    let pattern = Pattern pattern
    Console.OutputEncoding <- System.Text.Encoding.UTF8

    let generalizedPattern, vars2vars = Pattern.generalizeVariables pattern
    let instantiator = linearInstantiator generalizedPattern
    let A = pattern2a generalizedPattern
    let B = pattern2b generalizedPattern
    printQuery pattern vars2vars A B
    let A, B = printInstance instantiator A B
    let invariantA = printFinal A B
    let leftSide, rightSide = printInduction B invariantA
    let ok = printInductionSchema leftSide rightSide
    ok

let var n = Var (IdentGenerator.gensymp n)
let a, x, y = var "a", var "x", var "y"
let L = Apply(IdentGenerator.gensymp "L", [])
let binaryConstructor c = let c = IdentGenerator.gensymp c in fun (x, y) -> Apply(c, [x; y])
let N = binaryConstructor "N"
let unaryConstructor c = let c = IdentGenerator.gensymp c in fun x -> Apply(c, [x])
let S = unaryConstructor "S"

[<Test>]
let Test1 () =
    Assert.IsTrue(testPattern [a; N(x, y)])

[<Test>]
let Test2 () =
    Assert.IsTrue(testPattern [a; N(L, N(x, y))])

[<Test>]
let Test3 () =
    Assert.IsTrue(testPattern [x; N(x, x)])

[<Test>]
let Test4 () =
    Assert.IsTrue(testPattern [a; S(x)])

[<Test>]
let Test5 () =
    Assert.IsTrue(testPattern [a; S(S(x))])

[<Test>]
let Test6 () =
    Assert.IsTrue(testPattern [a; N(L, x)])

[<Test>]
let Test7 () =
    Assert.IsTrue(testPattern [a; N(x, N(y, L))])

[<Test>]
let Test8 () =
    Assert.IsTrue(testPattern [a; N(x, N(x, x))])
