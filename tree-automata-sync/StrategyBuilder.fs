module tree_automata_sync.StrategyBuilder

type MultiIndex(strategyWidth, strategyHeight) =
    let mutable i = 0
    let mutable j = -1

    member x.HasNext() = i * strategyHeight + j + 1 < strategyWidth * strategyHeight

    member x.Increment() =
        i <- i + (j + 1) / strategyHeight
        j <- (j + 1) % strategyHeight

    member x.SetAtCurrent(arr : 'a array array, value : 'a) =
        arr.[i].[j] <- value

    override x.ToString() = $"({i}, {j})"

type StrategyBuilder(width, vars) =
    let width = width
    let vars = vars
    let fullConvolution = List.init vars (fun i -> List.init width (fun j -> (i, j))) |> List.pairwiseProduct
    let fullConvolution = Seq.map List.toArray fullConvolution |> Array.ofSeq
    let strategyWidth, strategyHeight = pown width vars, vars
    let mask = Array.init strategyWidth (fun _ -> Array.init strategyHeight (fun _ -> true))

    let droppedElementPointer = MultiIndex(strategyWidth, strategyHeight)

    member private x.ApplyStrategy strategy (xss : 'a list list) =
        // List.length xss <= vars
        // for each i, List.length xss[i] = width
        // Ex: xss = [[A; B]; [C; D]], strategy = (full convolution) = [[(0, 0); (1, 0)]; [(0, 0); (1, 1)]; [(0, 1); (1, 0)]; [(0, 1); (1, 1)]]
        // Result: [[A; C]; [A; D]; [B; C]; [B; D]]
        let totalSize = List.length xss
        List.map (List.choose (fun (i, j) -> if i < totalSize then Some(xss.[i].[j]) else None)) strategy

    member x.Build() =
        printf $"Trying {droppedElementPointer}"
        let strategy =
            Seq.map2 (fun strategyLine maskLine -> Seq.zip strategyLine maskLine |> Seq.choose (fun (e, b) -> if b then Some e else None) |> List.ofSeq) fullConvolution mask
            |> List.ofSeq
        x.ApplyStrategy strategy

    member x.IsReducible() = droppedElementPointer.HasNext()

    member x.ImproveCurrentStrategy() =
        droppedElementPointer.Increment()
        droppedElementPointer.SetAtCurrent(mask, false)

    member x.BacktrackStrategy() =
        droppedElementPointer.SetAtCurrent(mask, true)
