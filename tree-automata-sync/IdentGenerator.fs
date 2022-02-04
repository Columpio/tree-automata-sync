module tree_automata_sync.IdentGenerator

open System.Collections.Generic
open System.Text.RegularExpressions

type private IdentGenerator() =
    let symbols = Dictionary<string, int>()

    member x.gensymp prefix =
        let prefixStr = prefix.ToString()
        let prefixStr = Regex.Replace(prefixStr, "[^a-zA-Z]", "")
        let prefixStr = if prefixStr = "" then "x" else prefixStr
        let prefixStrLow = prefixStr.ToLower()
        let counter = ref 0
        if symbols.TryGetValue(prefixStrLow, counter) then
            symbols.[prefixStrLow] <- counter.Value + 1
        else
            symbols.Add(prefixStrLow, 1)
        if counter.Value = 0 then prefixStr else $"%s{prefixStr}%d{counter.Value}"

let private idgen = IdentGenerator()

let gensymp prefix = idgen.gensymp prefix
let gensym () = gensymp "x"