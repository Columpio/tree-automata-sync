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

type LinearIndex(strategyWidth, strategyHeight) =
    let mutable i = -1

    member x.HasNext() = i + 1 < strategyWidth

    member x.Increment() =
        i <- i + 1

    member x.SetAtCurrent(arr : 'a array array, value : 'a) =
        arr.[i] <- Array.init strategyHeight (fun _ -> value)

    override x.ToString() = $"({i}, *)"

type strategy = (int * int) list list

type StrategyBuilder(width, vars) =
    let width = width
    let vars = vars
    let fullConvolution =
        List.init vars (fun i -> List.init width (fun j -> (i, j))) // for 2 2 gives [[(0, 0); (0, 1)]; [(1, 0); (1; 1)]]
        |> List.pairwiseProduct
    let fullConvolution = Seq.map List.toArray fullConvolution |> Array.ofSeq
    let strategyWidth, strategyHeight = pown width vars, vars
    let mask = Array.init strategyWidth (fun _ -> Array.init strategyHeight (fun _ -> true))

    let droppedElementPointer = LinearIndex(strategyWidth, strategyHeight)

    member private x.ApplyStrategy (strategy : strategy) (xss : 'a list list) =
        // List.length xss <= vars
        // for each i, List.length xss[i] = width
        // Ex: xss = [[A; B]; [C; D]], strategy = (full convolution) = [[(0, 0); (1, 0)]; [(0, 0); (1, 1)]; [(0, 1); (1, 0)]; [(0, 1); (1, 1)]]
        // Result: [[A; C]; [A; D]; [B; C]; [B; D]]
        // Ex: xss = [[A; B]] -> [[A]; [B]], but we have [[A]; [A]]
        let totalSize = List.length xss
        let modulo = pown width (vars - totalSize)
        strategy
        |> List.indexed
        |> List.choose (fun (i, x) -> if i % modulo = 0 then Some x else None)
        |> List.map (List.choose (fun (i, j) -> if i < totalSize then Some(xss.[i].[j]) else None))

    member x.Build() =
        let strategy =
            Seq.map2 (fun strategyLine maskLine -> Seq.zip strategyLine maskLine |> Seq.choose (fun (e, b) -> if b then Some e else None) |> List.ofSeq) fullConvolution mask
            |> List.ofSeq
        x.ApplyStrategy strategy

    member x.IsReducible() = droppedElementPointer.HasNext()

    member x.ImproveCurrentStrategy() =
        droppedElementPointer.Increment()
        droppedElementPointer.SetAtCurrent(mask, false)
        printf $"Trying to drop {droppedElementPointer}"

    member x.BacktrackStrategy() =
        droppedElementPointer.SetAtCurrent(mask, true)
