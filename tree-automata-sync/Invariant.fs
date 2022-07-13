module tree_automata_sync.Invariant

let fromConstructorsAndStates freeConstrs states =
    let saturateGroundPatterns = id //TODO: not implemented (because this idea is now not needed)
    let saturatedStates = saturateGroundPatterns states
    Invariant(freeConstrs, saturatedStates)

let private mapEachState f (Invariant(freeConstrs, states)) = Invariant(freeConstrs, List.map f states)

let instantiate instantiator = mapEachState (State.instantiate instantiator)

let mapAutomatonApplies f = mapEachState (State.mapAutomatonApplies f)

let unfoldAutomatonApplyRec strategy = mapEachState (State.unfoldAutomatonApplyRec strategy)

let private matchAutomatonApplyStates statePattern stateInstance =
    match statePattern, stateInstance with
    | AutomatonApply(namePat, termsPat), AutomatonApply(nameInst, termsInst) ->
        if namePat = nameInst then Pattern.matchPattern termsPat termsInst else None
    | _ -> __unreachable__()

let rewrite state (rewriteFromState, Invariant(rewriteToConstrs, rewriteToStates)) =
    let rec rewrite = function
        | AutomatonApply _ as a ->
            match matchAutomatonApplyStates rewriteFromState a with
            | Some(substConstrs, substStates) ->
                let constrs' = List.instantiate substConstrs rewriteToConstrs
                let states' = List.map (State.rewrite substConstrs substStates) rewriteToStates
                CombinedState(constrs', states')
            | None -> a
        | DeltaApply(name, constrs, states) -> DeltaApply(name, constrs, List.map rewrite states)
        | _ -> __notImplemented__()
    rewrite state

let collectAutomatonApplies (Invariant(_, states)) = states |> List.map State.collectAutomatonApplies |> Set.unionMany

let maxFunctionArity (Invariant(_, states)) = states |> List.map State.maxFunctionArity |> List.max
