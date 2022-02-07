[<AutoOpen>]
module tree_automata_sync.Prelude
open System

let inline __notImplemented__() = failwith "Not implemented!"
let inline __unreachable__() = failwith "Unreachable!"
let inline toString x = x.ToString()
let inline join (s : string) (ss : string list) = String.Join(s, ss)

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

type pattern =
 | Pattern of term list
 override x.ToString() =
     let (Pattern(pat)) = x
     pat |> List.map toString |> join ", "

type state =
    | SVar of ident
    | CombinedState of opname list * state list // ``Delay'' states
    | AutomatonApply of ident * pattern
    | DeltaApply of ident * opname list * state list
    override x.ToString() =
        match x with
        | SVar i -> i
        | AutomatonApply(name, pat) -> $"%s{name}[{pat}]"
        | CombinedState(constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""((%s{cs}), (%s{ss}))"""
        | DeltaApply(name, constrs, states) ->
            let cs = constrs |> List.map toString |> join ", "
            let ss = states |> List.map toString |> join ", "
            $"""delta%s{name}(%s{cs}, %s{ss})"""

type invariant =
    | Invariant of opname list * state list
    override x.ToString() =
        match x with
        | Invariant(freeConstrs, abstrValues) ->
            let freeConstrsStr = freeConstrs |> List.map toString |> join ", "
            $"""(({freeConstrsStr}), ({abstrValues |> List.map toString |> join ", "}))"""
