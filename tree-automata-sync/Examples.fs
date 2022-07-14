module test
open tree_automata_sync
open NUnit.Framework
open FsCheck
open System

type DeltaGenerator(aloud, patterns, constructor_max_width) =
    let mutable aloud = aloud

    let setAloud b =
        aloud <- b
        if aloud then Console.OutputEncoding <- System.Text.Encoding.UTF8
    let chooseGoodWidth =
        if constructor_max_width <= 0 then id else fun widthNew ->
        Assert.LessOrEqual(widthNew, constructor_max_width, $"Induction width {constructor_max_width} is less than constructor arity {widthNew}")
        constructor_max_width

    let linearInstantiator pattern =
        let var2depth = Pattern.collectVariableDepths pattern
        let patDepth = Pattern.depth pattern
        let width = chooseGoodWidth (Pattern.maxFunctionArity pattern)
        width, var2depth |> Map.map (fun _ depth -> Term.mkFullTree width (patDepth - depth))

    do setAloud aloud
    let width, strategyBuilder, initialMetadata =
        let patterns = List.map Pattern patterns
        let patterns = List.map Pattern.makeConstructorsConstant patterns
        let widthsAndCounts, initialMetadata =
            patterns |> List.map (fun pattern ->
                let automatonASize = Pattern.length pattern
                let generalizedPattern, vars2vars = Pattern.generalizeVariables pattern
                let variablesCount = Map.keys vars2vars |> Seq.length
                let width, instantiator = linearInstantiator generalizedPattern
                (width, max automatonASize variablesCount), (pattern, generalizedPattern, vars2vars, instantiator)) |> List.unzip

        let width = fst <| List.maxBy fst widthsAndCounts
        let variablesCount = snd <| List.maxBy snd widthsAndCounts

        width, StrategyBuilder.StrategyBuilder(width, variablesCount), initialMetadata

    let pattern2a pattern = AutomatonApply("A", pattern)
    let pattern2b pattern =
        let pattern' = pattern |> Pattern.freeVars |> Set.toList |> List.map Var                                                 // each variable one time
    //    let pattern' = pattern |> Pattern.freeVarsMap |> Map.toList |> List.collect (fun (v, n) -> List.init n (fun _ -> Var v)) // each variable n times
        AutomatonApply("B", Pattern pattern')

    let printQuery pattern vars2vars A B =
        let vars2vars = Map.toList vars2vars
        let origVars = vars2vars |> List.map snd |> Set.ofList |> Set.toList
        if aloud then printfn $"""Хотим: L(C) = {{ ({join "," origVars}) | ({pattern}) \in L(A) }}"""
        if aloud then printfn $"""Построим: {B} \in Fb <=> {A} \in Fa"""
        let newVars = match B with AutomatonApply(_, Pattern ts) -> List.map (function Var ident -> ident | _ -> __unreachable__()) ts | _ -> __unreachable__()
        if aloud then printfn $"""Так что: L(C) = {{ ({join ", " origVars}) | \exists ({join ", " newVars}) \in L(B), {vars2vars |> List.map (fun (n, o) -> $"{n} = {o}") |> join ", "} }}"""
        if aloud then printfn ""

    let printInstance strategy instantiator A B =
        let A' = State.instantiate instantiator A
        let B' = State.instantiate instantiator B
        if aloud then printfn "Инстанцируем:"
        if aloud then printfn $"""{B'} \in Fb <=>"""
        if aloud then printfn $"""  Fa \ni {A'} ="""
        let A'' = State.unfoldAutomatonApplyRec strategy A'
        if aloud then printfn $"\t {A''}"
        if aloud then printfn ""
        A'', B'

    let printFinal A B =
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

    let printInductionSchema leftSide rightSide =
        if aloud then printfn "Соединение левой и правой части:"
        if aloud then printfn $"{leftSide} =\n\t{rightSide}\n"

        let callsDiff = Invariant.difference rightSide leftSide
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

    let prepareInduction state =
        let freeVars = State.freeVars state |> Set.toList
        freeVars
        |> List.map (fun ident -> ident, Term.mkFullTree width 1)
        |> Map.ofList

    let printInduction strategy B invariantA =
        let instantiator = prepareInduction B
        if aloud then printfn "Индукционная раскрутка слева:"
        let B' = State.instantiate instantiator B
        if aloud then printfn $"{B'} ="
        let B'' = State.unfoldAutomatonApplyOnce strategy B'
        if aloud then printfn $"\t{B''} ="
        let sideB = Invariant.rewrite B'' (B, invariantA)
        if aloud then printfn $"\t{sideB}"
        if aloud then printfn ""

        let invariantA' = Invariant.instantiate instantiator invariantA
        let invariantA'' = Invariant.unfoldAutomatonApplyRec strategy invariantA'
        if aloud then printfn "Индукционная раскрутка справа:"
        if aloud then printfn $"{invariantA'} ="
        if aloud then printfn $"\t{invariantA''}"
        if aloud then printfn ""

        sideB, invariantA''

    let checkStrategyIsNotEmpty strategy A =
        let instantiator = prepareInduction A
        let instA = State.instantiate instantiator A
        let unfoldedA = State.unfoldAutomatonApplyOnce strategy instA
        State.isVarSubset instA unfoldedA

    new (aloud, patterns) = DeltaGenerator(aloud, patterns, 0)
    new (aloud, pattern) = DeltaGenerator(aloud, [pattern])

    member x.StrategyBuilder = strategyBuilder

    member x.CheckAloud () =
        setAloud true
        x.Check()

    member x.Check () =
        let strategy = strategyBuilder.Build()
        seq {
            for pattern, generalizedPattern, vars2vars, instantiator in initialMetadata do
                let A = pattern2a generalizedPattern
                yield checkStrategyIsNotEmpty strategy A
                let B = pattern2b generalizedPattern
                printQuery pattern vars2vars A B
                let A, B = printInstance strategy instantiator A B
                let invariantA = printFinal A B
                let leftSide, rightSide = printInduction strategy B invariantA
                let ok = printInductionSchema leftSide rightSide
                yield ok
        } |> Seq.forall id

let var n = Var (IdentGenerator.gensymp n)
let zeroaryConstructor c = let c = IdentGenerator.gensymp c in Apply(c, [])
let unaryConstructor c = let c = IdentGenerator.gensymp c in fun x -> Apply(c, [x])
let binaryConstructor c = let c = IdentGenerator.gensymp c in fun (x, y) -> Apply(c, [x; y])

let a, x, y, z, b = var "a", var "x", var "y", var "z", var "b"
let L = zeroaryConstructor "L"
let N = binaryConstructor "N"
let S = unaryConstructor "S"
let nil = zeroaryConstructor "nil"
let cons = binaryConstructor "cons"

let testAloud (pattern : term list) = Assert.IsTrue <| DeltaGenerator(true, pattern).Check()
let testSilent (pattern : term list) = Assert.IsTrue <| DeltaGenerator(false, pattern).Check()

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

[<Test>]
let Test9 () =
    testAloud [N(x, y); z]

// \phi -> invariant -> full conv. automaton -> closed modulo **all possible** patterns
// \phi -> invariant -> some conv. automaton -> closed modulo patterns of \phi?
// 
[<Test>]
let Test10 () =
    testAloud [x; N(N(L, L), N(L, L))]

let TestMultiplePatternsSchemaCover patterns =
    let g = DeltaGenerator(false, patterns, 2)
    let mutable ok = true
    while ok do
        if not <| g.Check() then
            printfn ": stays"
            g.StrategyBuilder.BacktrackStrategy()
        else printfn ""
        if g.StrategyBuilder.IsReducible() then
            g.StrategyBuilder.ImproveCurrentStrategy()
        else
            ok <- false
    IdentGenerator.reset()
    Assert.IsTrue(g.CheckAloud())

[<Test>]
let TestMultiplePatternsSchemaCover1 () =
    let patterns = [
        [nil; cons(x, y)]
        [cons(x, y); cons(a, b)]
        [x; y]
    ]
    TestMultiplePatternsSchemaCover patterns

[<Test>]
let TestMultiplePatternsSchemaCover2 () =
    let patterns = [
        [x; y]
    ]
    TestMultiplePatternsSchemaCover patterns

[<Test>]
let TestMultiplePatternsSchemaCover3 () =
    let patterns = [
        [cons(x, y); cons(a, b)]
    ]
    TestMultiplePatternsSchemaCover patterns

[<Test>]
let TestMultiplePatternsSchemaCover4 () =
    let patterns = [
        [x; x]
    ]
    TestMultiplePatternsSchemaCover patterns

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
