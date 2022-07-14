module tree_automata_sync.State

let mapAutomatonApplies f =
    let rec mapPattern = function
        | SVar _ as v -> v
        | AutomatonApply(name, pattern) -> f name pattern
        | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map mapPattern states)
        | CombinedState(constrs, states) -> CombinedState(constrs, List.map mapPattern states)
    mapPattern

let foldAutomatonApplies fIdent f =
    let rec fold z = function
        | SVar i -> fIdent z i
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

let freeConstructors =
    let rec freeConstructors free state =
        match state with
        | DeltaApply(_, constrs, states) ->
            List.fold freeConstructors (constrs |> List.filter Op.isConstructorFree |> Set.ofList |> Set.union free) states
        | _ -> free
    freeConstructors Set.empty >> Set.toList

let instantiate instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.instantiate instantiator pat))
let rewrite substConstrs instantiator = mapAutomatonApplies (fun name pat -> AutomatonApply(name, Pattern.rewrite substConstrs instantiator pat))

let unfoldAutomatonApplyGeneric strategy mapChild =
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
            let states = strategy bodies |> List.choose (fun pat -> if pat = [] then None else Some <| AutomatonApply(name, Pattern pat))
            let states = List.map mapChild states
            DeltaApply(name, heads, states)
        | None -> AutomatonApply(name, pattern)
    mapAutomatonApplies unfoldAutomatonApply

let unfoldAutomatonApplyOnce strategy = unfoldAutomatonApplyGeneric strategy id
let unfoldAutomatonApplyRec strategy =
    let rec iter state = unfoldAutomatonApplyGeneric strategy iter state
    iter

let freeVars = foldAutomatonApplies (fun free i -> Set.add i free) (fun free _ -> Pattern.freeVars >> Set.union free) Set.empty

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

let collectAutomatonApplies = foldAutomatonApplies (fun z _ -> z) (fun states name pat -> Set.add (AutomatonApply(name, pat)) states) Set.empty

let maxFunctionArity = foldAutomatonApplies (fun z _ -> z) (fun mx _ pat -> max mx (Pattern.maxFunctionArity pat)) 0

let isVarSubset left right =
    // left \subseteq right <=> left \ right = \emptyset
    let callsLeft = freeVars left
    let callsRight = freeVars right
    let callsDiff = Set.difference callsLeft callsRight
    Set.isEmpty callsDiff
