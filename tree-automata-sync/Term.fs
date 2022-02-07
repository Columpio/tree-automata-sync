[<AutoOpen>]
module tree_automata_sync.Term

module Term =
    let foldWithDepth z fIdent fOpname =
        let rec foldWithDepth depth z = function
            | Var i -> fIdent i depth z
            | Apply(op, ts) -> List.fold (foldWithDepth (depth + 1)) (fOpname op depth z) ts
        foldWithDepth 0 z

    let fold fIdent fOpname =
        let rec fold z = function
            | Var i -> fIdent i z
            | Apply(op, ts) -> List.fold fold (fOpname op z) ts
        fold

    let map fIdent fOpname =
        let rec map = function
            | Var i -> fIdent i
            | Apply(op, ts) -> Apply(fOpname op, List.map map ts)
        map

    let mapFold fIdent fOpname =
        let rec iter z = function
            | Var i -> fIdent i z
            | Apply(op, ts) ->
                let op, z = fOpname op z
                let ts, z = List.mapFold iter z ts
                Apply(op, ts), z
        iter

    let toLinearString = fold List.cons List.cons [] >> List.rev >> join ""

    let mapVars f = map f id

    let freeVars = fold Set.add (fun _ -> id) Set.empty
    let freeVarsMap = fold Counter.add (fun _ -> id) Counter.empty

    let Bottom = Apply("Bot", [])

    let isBottom = (=) Bottom

    let mkFreshVar () = Var (IdentGenerator.gensym ())
    
    let mkApplyNary N prefix init = Apply(IdentGenerator.gensymp prefix, List.init N init)

    let mkFullTree width height =
        let rec iter height = if height <= 0 then mkFreshVar () else mkApplyNary width "f" (fun _ -> iter (height - 1))
        iter height
    
    let cut = function
        | Var _ -> None
        | Apply(opname, args) -> Some(opname, args)

    let private trySubstituteIdent map ident = Map.findOrApply Var map ident

    let instantiate instantiator = mapVars (trySubstituteIdent instantiator)
    
    let rewrite substConstrs instantiator = map (trySubstituteIdent instantiator) (Map.findOrDefault substConstrs)

    let substitute constrMap varMap = map (trySubstituteIdent varMap) (Map.findOrDefault constrMap)

    let maxFunctionArity =
        let rec iter mx = function
            | Var _ -> mx
            | Apply(_, ts) -> List.fold iter (max mx <| List.length ts) ts
        iter 0

    let depth = foldWithDepth 0 (fun _ -> max) (fun _ d -> max (d + 1))
        

module TermList =
    let isBottoms = List.forall Term.isBottom

    let freeVars = List.map Term.freeVars >> Set.unionMany
    let freeVarsMap = List.map Term.freeVarsMap >> Counter.unionMany

    let generalizeVariables ts =
        let generalizeVar ident map =
            let ident' = IdentGenerator.gensymp ident
            Var ident', Map.add ident' ident map
        List.mapFold (Term.mapFold generalizeVar (fun op map -> op, map)) Map.empty ts

    let instantiate instantiator = List.map (Term.instantiate instantiator)
    
    let rewrite substConstrs instantiator = List.map (Term.rewrite substConstrs instantiator)

    let cutHeads = List.mapChoose Term.cut >> Option.map List.unzip

module Pattern =
    let freeVars (Pattern pat) = TermList.freeVars pat
    let freeVarsMap (Pattern pat) = TermList.freeVarsMap pat
    let generalizeVariables (Pattern pat) =
        let pat', vars2vars = TermList.generalizeVariables pat
        Pattern pat', vars2vars
    
    let matchPattern (Pattern termsPat) (Pattern termsInst) =
        let rec matchWith ((constrMap, varMap) as maps) (termPat, termInst) k =
            match termPat with
            | Apply(fPat, argsPat) ->
                match termInst with
                | Apply(fInst, argsInst) ->
                    match Map.tryFind fPat constrMap with
                    | Some f when f = fInst ->
                        matchListsWith maps (List.zip argsPat argsInst) k
                    | Some _ -> None
                    | None ->
                        let maps = Map.add fPat fInst constrMap, varMap
                        matchListsWith maps (List.zip argsPat argsInst) k
                | Var _ -> None
            | Var idPat ->
                match Map.tryFind idPat varMap with
                | Some t when t = termInst -> k maps
                | Some _ -> None
                | None -> k (constrMap, Map.add idPat termInst varMap)
        and matchListsWith maps pairs k = List.kfoldk matchWith maps pairs k
        matchListsWith (Map.empty, Map.empty) (List.zip termsPat termsInst) Some

    let instantiate instantiator (Pattern pat) = Pattern(TermList.instantiate instantiator pat)
    let rewrite substConstrs instantiator (Pattern pat) = Pattern(TermList.rewrite substConstrs instantiator pat)

    let cutHeads (Pattern pat) =
        if TermList.isBottoms pat then None else TermList.cutHeads pat

    let maxFunctionArity (Pattern pat) = List.max <| List.map Term.maxFunctionArity pat

    let depth (Pattern pat) = List.max <| List.map Term.depth pat
    
    let collectVariableDepths (Pattern pat) =
        List.fold (fun vars2depths -> Term.foldWithDepth vars2depths Map.add (fun _ _ -> id)) Map.empty pat
