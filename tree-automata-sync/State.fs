module tree_automata_sync.State
open System

let mapAutomatonApplies f =
    let rec mapPattern = function
        | SVar _ as v -> v
        | AutomatonApply(name, pattern) -> f name pattern
        | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map mapPattern states)
        | CombinedState(constrs, states) -> CombinedState(constrs, List.map mapPattern states)
    mapPattern

let foldAutomatonApplies f =
    let rec fold z = function
        | SVar _ -> z
        | AutomatonApply(name, pattern) -> f z name pattern
        | CombinedState(_, states)
        | DeltaApply(_, _, states) -> List.fold fold z states
    fold

let mapFoldAutomatonApplies f =
    let rec mapFold z = function
        | SVar _ as v -> v, z
        | AutomatonApply(name, pattern) -> f z name pattern
        | DeltaApply(name, heads, states) ->
            let states, z = List.mapFold mapFold z states
            DeltaApply(name, heads, states), z
        | CombinedState(heads, states) ->
            let states, z = List.mapFold mapFold z states
            CombinedState(heads, states), z
    mapFold

let private isConstructorFree (op : string) = op.Chars(0) |> Char.IsLower //TODO

let freeConstructors =
    let rec freeConstructors free state =
        match state with
        | DeltaApply(_, constrs, states) ->
            List.fold freeConstructors (constrs |> List.filter isConstructorFree |> Set.ofList |> Set.union free) states
        | _ -> free
    freeConstructors Set.empty >> Set.toList

let instantiate instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.instantiate instantiator pat))
let rewrite substConstrs instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.rewrite substConstrs instantiator pat))

let private unfoldAutomatonApplyGeneric mapChild =
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
            let states = List.pairwiseProduct bodies |> List.map (fun pat -> AutomatonApply(name, Pattern pat))
            let states = List.map mapChild states
            DeltaApply(name, heads, states)
        | None -> AutomatonApply(name, pattern)
    mapAutomatonApplies unfoldAutomatonApply

let unfoldAutomatonApplyOnce = unfoldAutomatonApplyGeneric id
let rec unfoldAutomatonApplyRec state = unfoldAutomatonApplyGeneric unfoldAutomatonApplyRec state

let freeVars = foldAutomatonApplies (fun free _ -> Pattern.freeVars >> Set.union free) Set.empty

let abstractAutomatonApplies =
    let nameFromPattern (Pattern pat) =
        pat
        |> List.map Term.toLinearString
        |> join ""
        |> IdentGenerator.gensymp
    let helper ((vars2states, states2vars) as maps) name pat =
        let a = AutomatonApply(name, pat)
        match Map.tryFind a states2vars with
        | Some ident -> SVar ident, maps
        | None ->
            let freshName = nameFromPattern pat
            SVar freshName, (Map.add freshName a vars2states, Map.add a freshName states2vars)
    mapFoldAutomatonApplies helper (Map.empty, Map.empty)

let collectAutomatonApplies = foldAutomatonApplies (fun states name pat -> Set.add (AutomatonApply(name, pat)) states) Set.empty

let maxFunctionArity = foldAutomatonApplies (fun mx _ pat -> max mx (Pattern.maxFunctionArity pat)) 0
