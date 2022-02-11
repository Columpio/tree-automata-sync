module test
open tree_automata_sync
open NUnit.Framework
open FsCheck
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

let printQuery aloud pattern vars2vars A B =
    let vars2vars = Map.toList vars2vars
    let origVars = vars2vars |> List.map snd |> Set.ofList |> Set.toList
    if aloud then printfn $"""Хотим: L(C) = {{ ({join "," origVars}) | ({pattern}) \in L(A) }}"""
    if aloud then printfn $"""Построим: {B} \in Fb <=> {A} \in Fa"""
    let newVars = match B with AutomatonApply(_, Pattern ts) -> List.map (function Var ident -> ident | _ -> __unreachable__()) ts | _ -> __unreachable__()
    if aloud then printfn $"""Так что: L(C) = {{ ({join ", " origVars}) | \exists ({join ", " newVars}) \in L(B), {vars2vars |> List.map (fun (n, o) -> $"{n} = {o}") |> join ", "} }}"""
    if aloud then printfn ""

let printInstance aloud instantiator A B =
    let A' = State.instantiate instantiator A
    let B' = State.instantiate instantiator B
    if aloud then printfn "Инстанцируем:"
    if aloud then printfn $"""{B'} \in Fb <=>"""
    if aloud then printfn $"""  Fa \ni {A'} ="""
    let A'' = State.unfoldAutomatonApplyRec A'
    if aloud then printfn $"\t {A''}"
    if aloud then printfn ""
    A'', B'

let printFinal aloud A B =
    if aloud then printfn "Положим:"
    let abstrState, (abstrVarsMap, _) = State.abstractAutomatonApplies A
    let abstrVars = abstrVarsMap |> Map.toList |> List.map fst
    let freeConstrs = State.freeConstructors abstrState
    let freeConstrsStr = freeConstrs |> List.map toString |> join ", "
    if aloud then printfn $"""Fb := {{ (({freeConstrsStr}), ({abstrVars |> List.map toString |> join ", "})) |{"\n\t"}{abstrState} \in Fa }}"""
    if aloud then printfn ""
    if aloud then printfn "Тогда инвариант:"
    let inv = Invariant.fromConstructorsAndStates freeConstrs (List.map (Map.findOrApply SVar abstrVarsMap) abstrVars)
    if aloud then printfn $"{B} =\n\t{inv}\n"
    inv

let printInduction aloud B invariantA =
    let freeVars = State.freeVars B |> Set.toList
    let width = max (State.maxFunctionArity B) (Invariant.maxFunctionArity invariantA)
    let instantiator=
        freeVars
        |> List.map (fun ident -> ident, Term.mkFullTree width 1)
        |> Map.ofList
    if aloud then printfn "Индукционная раскрутка слева:"
    let B' = State.instantiate instantiator B
    if aloud then printfn $"{B'} ="
    let B'' = State.unfoldAutomatonApplyOnce B'
    if aloud then printfn $"\t{B''} ="
    let sideB = Invariant.rewrite B'' (B, invariantA)
    if aloud then printfn $"\t{sideB}"
    if aloud then printfn ""

    let invariantA' = Invariant.instantiate instantiator invariantA
    let invariantA'' = Invariant.unfoldAutomatonApplyRec invariantA'
    if aloud then printfn "Индукционная раскрутка справа:"
    if aloud then printfn $"{invariantA'} ="
    if aloud then printfn $"\t{invariantA''}"
    if aloud then printfn ""

    sideB, invariantA''

let printInductionSchema aloud leftSide rightSide =
    if aloud then printfn "Соединение левой и правой части:"
    if aloud then printfn $"{leftSide} =\n\t{rightSide}\n"

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
        if aloud then printfn "Итоговая индукционная схема:"
        if aloud then printfn $"{abstrLeftSide} =\n\t{abstrRightSide}"
        true
    else
        if aloud then printfn "Что из правой части не хватает в левой:"
        if aloud then printfn $"""Количество: {Set.count callsDiff}, Состояния: {callsDiff |> Seq.map toString |> join ", "}."""
        false

let testPattern aloud pattern =
    let pattern = Pattern pattern
    if aloud then Console.OutputEncoding <- System.Text.Encoding.UTF8

    let generalizedPattern, vars2vars = Pattern.generalizeVariables pattern
    let instantiator = linearInstantiator generalizedPattern
    let A = pattern2a generalizedPattern
    let B = pattern2b generalizedPattern
    printQuery aloud pattern vars2vars A B
    let A, B = printInstance aloud instantiator A B
    let invariantA = printFinal aloud A B
    let leftSide, rightSide = printInduction aloud B invariantA
    let ok = printInductionSchema aloud leftSide rightSide
    Assert.IsTrue(ok)

let testSilent = testPattern false
let testAloud = testPattern true

let var n = Var (IdentGenerator.gensymp n)
let a, x, y = var "a", var "x", var "y"
let L = Apply(IdentGenerator.gensymp "L", [])
let binaryConstructor c = let c = IdentGenerator.gensymp c in fun (x, y) -> Apply(c, [x; y])
let N = binaryConstructor "N"
let unaryConstructor c = let c = IdentGenerator.gensymp c in fun x -> Apply(c, [x])
let S = unaryConstructor "S"

[<SetUp>]
let initTest () =
    IdentGenerator.reset ()

[<Test>]
let Test1 () =
    testAloud [a; N(x, y)]

[<Test>]
let Test2 () =
    testAloud [a; N(L, N(x, y))]

[<Test>]
let Test3 () =
    testAloud [x; N(x, x)]

[<Test>]
let Test4 () =
    testAloud [a; S(x)]

[<Test>]
let Test5 () =
    testAloud [a; S(S(x))]

[<Test>]
let Test6 () =
    testAloud [a; N(L, x)]

[<Test>]
let Test7 () =
    testAloud [a; N(x, N(y, L))]

[<Test>]
let Test8 () =
    testAloud [a; N(x, N(x, x))]

type patternSetup = {termWidth: int; termHeight: int; varNumber: int; constrNumber: int; termsInPattern: int}
type testSetup = {patternSetup: patternSetup; runTimes: int}

let generatePattern (setup : patternSetup) =
    let vars = List.init setup.varNumber (fun _ -> IdentGenerator.gensym ())
    let constrs = List.init setup.constrNumber (fun _ -> IdentGenerator.gensym ())
    let maxHeight = setup.termHeight
    let rec generateTerm height =
        let genVar =
            gen {
                let! ident = Gen.elements vars
                return Var ident
            }
        let genApply =
            gen {
                let! args = Gen.listOfLength setup.termWidth (generateTerm (height + 1))
                let! op = Gen.elements constrs
                return Apply(op, args)
            }
        if height >= maxHeight then genVar
        else
            Gen.frequency [
                height + 1, genVar
                maxHeight - height, genApply
            ]
    Gen.listOfLength setup.termsInPattern (generateTerm 0)

let generateAndRunTest (setup : testSetup) =
    let generator = generatePattern setup.patternSetup
    let size = Int32.MaxValue
    for pattern in Gen.sample size setup.runTimes generator do
        printfn $"{Pattern pattern}"
        testSilent pattern
        initTest ()

[<Test>]
let SmallBinaryRun1 () =
    let setup = {patternSetup = {termWidth = 2; termHeight = 1; varNumber = 2; constrNumber = 3; termsInPattern = 3}; runTimes = 30}
    generateAndRunTest setup

[<Test>]
let SmallBinaryRun2 () =
    let setup = {patternSetup = {termWidth = 2; termHeight = 2; varNumber = 4; constrNumber = 3; termsInPattern = 3}; runTimes = 30}
    generateAndRunTest setup

[<Test>]
let SmallBinaryRun3 () =
    let setup = {patternSetup = {termWidth = 2; termHeight = 2; varNumber = 10; constrNumber = 10; termsInPattern = 3}; runTimes = 30}
    generateAndRunTest setup

[<Test>]
let SmallTrinaryRun1 () =
    let setup = {patternSetup = {termWidth = 3; termHeight = 1; varNumber = 10; constrNumber = 10; termsInPattern = 2}; runTimes = 30}
    generateAndRunTest setup

[<Test>]
let SmallTrinaryRun2 () =
    let setup = {patternSetup = {termWidth = 3; termHeight = 1; varNumber = 10; constrNumber = 10; termsInPattern = 3}; runTimes = 30}
    generateAndRunTest setup
