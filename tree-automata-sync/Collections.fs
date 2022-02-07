[<AutoOpen>]
module tree_automata_sync.Collections

module Map =
    let findOrDefault map x = Map.tryFind x map |> Option.defaultValue x

    let findOrApply f map x = Map.tryFind x map |> Option.defaultWith (fun () -> f x)
    
    let findOrAdd f x map =
        match Map.tryFind x map with
        | Some y -> y, map
        | None ->
            let y = f x
            y, Map.add x y map

module List =
    let kfoldk f =
        let rec kfoldk z xs k =
            match xs with
            | [] -> k z
            | x::xs -> f z x (fun y -> kfoldk y xs k)
        kfoldk

    let inline cons x xs = x :: xs

    let mapChoose f xs =
        let rec mapChoose xs k =
            match xs with
            | [] -> k []
            | x::xs ->
                match f x with
                | Some y -> mapChoose xs (fun ys -> k (y::ys))
                | None -> None
        mapChoose xs Some

    let instantiate map = List.map (Map.findOrDefault map)

    let pairwiseProduct xss =
        let rec product xss k =
            match xss with
            | [] -> k [[]]
            | xs::xss ->
                product xss (fun yss -> xs |> List.collect (fun x -> List.map (fun ys -> x :: ys) yss) |> k)
        product xss id

module Counter =
    let empty : Map<'a, int> = Map.empty

    let addMany x m c =
        match Map.tryFind x c with
        | Some n -> Map.add x (n + m) c
        | None -> Map.add x m c
    
    let add x c = addMany x 1 c

    let union cBig cSmall = Map.foldBack addMany cSmall cBig
    
    let unionMany cs = List.fold union empty cs
