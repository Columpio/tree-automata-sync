module tree_automata_sync.StrategyBuilder

type StrategyBuilder(width, vars) =
    let width = width
    let vars = vars

    let mutable wasRunOnce = false

    let mutable strategy = // full convolution
        List.init vars (fun i -> List.init width (fun j -> (i, j)))
        |> List.pairwiseProduct

    member private x.ApplyStrategy strategy (xss : 'a list list) =
        // List.length xss <= vars
        // for each i, List.length xss[i] = width
        // Ex: xss = [[A; B]; [C; D]], strategy = (full convolution) = [[(0, 0); (1, 0)]; [(0, 0); (1, 1)]; [(0, 1); (1, 0)]; [(0, 1); (1, 1)]]
        // Result: [[A; C]; [A; D]; [B; C]; [B; D]]
        let totalSize = List.length xss
        List.map (List.choose (fun (i, j) -> if i < totalSize then Some(xss.[i].[j]) else None)) strategy

    member x.Build() = x.ApplyStrategy strategy

    member x.IsReducible() = not wasRunOnce

    member x.ImproveCurrentStrategy() = wasRunOnce <- true

    member x.BacktrackStrategy() = __notImplemented__()
