module RInGen.TtaTransform

open Microsoft.FSharp.Collections
open RInGen
open RInGen.IdentGenerator

let stateSort = gensymp "State" |> PrimitiveSort

type pattern = Pattern of string * term list

type AutomataRecord =
    { initConst : term
      isFinal : operation
      delta : operation
      reach: operation }

let notop = Operation.makeElementaryRelationFromSorts "not" [boolSort]

type Processer(adts) =
    // TODO: optimization
    let m = adts |> List.map snd |> List.concat |> List.map snd |> List.map (List.length) |> List.max
    member private x.getEqRelName s =
        "eq" + s.ToString()
    member private x.getDiseqRelName s =
        "diseq" + s.ToString()

    member x.generateAutomataDeclarations name sortList =
        let initStateName = "init_" + name
        let isFinalName = "isFinal_" + name
        let deltaName = "delta_" + name
        let reachName = "reach_" + name
        
        let decls =
            let initStateDecl = DeclareConst (initStateName, stateSort)
            let isFinalDecl = DeclareFun(isFinalName, [stateSort], boolSort)
            let deltaDecl = DeclareFun(deltaName, sortList @ [stateSort], stateSort)
            let reachDecl = DeclareFun(reachName, [stateSort], boolSort)
            [initStateDecl; isFinalDecl; deltaDecl; reachDecl]
        
        let aRec =
            let initState = TConst(initStateName, stateSort)
            let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
            let mStatesVec = List.init m (fun _ -> stateSort)
            let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ mStatesVec) stateSort
            let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]
            {initConst = initState; isFinal = isFinal; delta = delta; reach=reach}
        
        List.map OriginalCommand decls, aRec

    member x.processDeclarations oCommands =
        let getDecls el =
            match el with
            | DeclareFun(fname, args, _) ->
                let decls, _ = x.generateAutomataDeclarations fname args
                Some decls
            | _ -> None

        let xs = oCommands |> List.map getDecls |> List.filter (fun el -> el.IsSome)

        seq {
            for el in xs do
                match el with
                | Some c -> yield! c
                | None -> ()
        }

    member x.parseDatatypes adts =
        let processDt(s, xs) =
            let constructors = List.map (fun x -> DeclareConst (fst x, s)) xs
            let bot = DeclareConst(s.getBotSymbol(), s)
            let baseDecls =
                 List.map OriginalCommand ([DeclareSort(s); bot] @ constructors)
            // eq axioms
            let automataDecls, eqRec =
                let eqRelName = x.getEqRelName s
                x.generateAutomataDeclarations eqRelName [s; s]

            let initAxiom =
                let r = AApply(eqRec.isFinal, [eqRec.initConst])
                TransformedCommand (rule [] [] r)
            let deltaAxiom =
                let qVar = ("q", stateSort)
                let qTerm = TIdent qVar
                let fVar, gVar = ("f", s), ("g", s)
                let fTerm, gTerm = TIdent fVar, TIdent gVar
                let l = AApply(eqRec.isFinal, [TApply(eqRec.delta, [fTerm; gTerm; qTerm])])
                let r = [AApply(equal_op s, [fTerm; gTerm]); AApply(eqRec.isFinal, [qTerm])]
                let forallQuant = ForallQuantifier([qVar; fVar; gVar])
                TransformedCommand (Equivalence([forallQuant], r, l))
            
            // TODO: diseq + diseqAxioms ??
            // Note : diseq decls are generated twice, see parseDeclarations
            baseDecls @ automataDecls @ [initAxiom; deltaAxiom]

        seq {
            for c in adts do
                yield! (processDt c)
        }

    member x.generatePosAxioms atom posRecord baseRecord =
        let pattern =
            match atom with
            | AApply(_, ts) -> ts
            | Equal(t1, t2) | Distinct(t1, t2) ->
                [t1; t2]
            | Bot |Top -> __unreachable__()
        
        let isIdent t =
            match t with
            | TIdent(_, _) -> true
            | _ -> false
        let isConstructor t = not (isIdent t)
        
        let mStateVars = List.init m (fun _ -> (gensym(), stateSort))
        let mStateVec = List.map TIdent mStateVars

        let allVars = pattern |> List.map isIdent |> List.fold (&&) true
        if allVars then
            let vars = x.CollectFreeVarsInTerms pattern
            let ordVars = pattern |> List.sort
            let l = TApply(posRecord.delta, ordVars @ mStateVec)
            let r = TApply(baseRecord.delta, pattern @ mStateVec)
            let deltaRule = rule (mStateVars @ vars) [] (AApply(equal_op stateSort, [l; r]))
            let q = TIdent("q", stateSort)
            let isFinalRule = eqRule [("q", stateSort)] [AApply(posRecord.isFinal, [q])] (AApply(baseRecord.isFinal, [q]))
            [isFinalRule; deltaRule]
        else
        
        let allConstructors = pattern |> List.map isConstructor |> List.fold (&&) true
        if allConstructors then  
            let getFirstConstrucror t =
                match t with
                | TConst(name, s) -> TConst(name, s)
                | TApply(op,_) -> TConst(op.ToString(), op.getSort())
                | _ -> __unreachable__()

            let q = TIdent("q", stateSort)
            let constrs = pattern |> List.map getFirstConstrucror
            let isFinalLeft = AApply(posRecord.isFinal, [q])
            let isFinalRight = AApply(baseRecord.isFinal, [TApply(baseRecord.delta, constrs @ [q])])
            let isFinalRule = eqRule [("q", stateSort)] [isFinalLeft] isFinalRight
            
            let getNextConstructor t =
                match t with
                | TConst(_, s) -> [TConst(s.getBotSymbol(), s)]
                | TApply(op, ts) ->
                    if List.isEmpty ts then
                        let s = op.getSort()
                        [TConst(s.getBotSymbol(), s)]
                    else ts
                | TIdent(_, _) -> __unreachable__()
            
            let rVec =  pattern |> List.map getNextConstructor |> List.concat
            let rVars = x.CollectFreeVarsInTerms rVec
            let deltaRight = TApply(baseRecord.delta, rVec @ mStateVec)
            let lVec = rVars |> List.sort |> List.map TIdent
            let deltaLeft = TApply(posRecord.delta, lVec @ mStateVec)
            let deltaRule = AApply(equal_op stateSort, [deltaLeft; deltaRight])
            let deltaRule = rule (mStateVars @ rVars) [] deltaRule
            [isFinalRule; deltaRule]
            
        else
            __notImplemented__()
    
    member private x.CollectFreeVarsInTerm = function
        | TIdent(i, s) -> [i, s]
        | TConst _ -> []
        | TApply(_, ts) -> x.CollectFreeVarsInTerms ts

    member private x.CollectFreeVarsInTerms = List.collect x.CollectFreeVarsInTerm
    
    member private x.CollectFreeVarsInAtom = function
       | AApply(_, ts) -> x.CollectFreeVarsInTerms ts
       | Equal(t1, t2) | Distinct(t1, t2) -> x.CollectFreeVarsInTerms [t1; t2]
       | Bot | Top -> []
    member private x.CollectFreeVarsInAtoms = List.collect x.CollectFreeVarsInAtom

    member x.procAtom clauseNum posNum atom =
        let posName = "pos_C" + clauseNum.ToString() + "_" + posNum.ToString()
        let baseName, baseSortList, posVarList =
            match atom with
            | Bot | Top -> "", [], []
            | Equal(t1, t2) ->
                let s = t1.getSort()
                x.getEqRelName s, [s; s], x.CollectFreeVarsInTerms [t1; t2]
            | Distinct(t1, t2) ->
                let s = t1.getSort()
                x.getDiseqRelName s, [s; s], x.CollectFreeVarsInTerms [t1; t2]
            | AApply(op, ts) -> op.ToString(), List.map (fun (t: term) -> t.getSort()) ts, x.CollectFreeVarsInTerms ts
        
        if List.isEmpty baseSortList then None else
        
        let posSortList = List.map snd posVarList
        let posDecls, posRecord = x.generateAutomataDeclarations posName posSortList
        let _, baseRecord = x.generateAutomataDeclarations baseName baseSortList
        let initAxiom = AApply(equal_op stateSort, [posRecord.initConst; baseRecord.initConst]) 
        let initAxiom = rule [] [] initAxiom
        let posAxioms = x.generatePosAxioms atom posRecord baseRecord
        Some(posRecord, posDecls @ List.map TransformedCommand ([initAxiom] @ posAxioms))

    member x.procRule clauseNum r =
        let body, head =
            match r with
            | Rule(_,body, head) -> body, head
            | _ -> __unreachable__()

        let atoms = body @ [head]
        let positions, axioms = atoms |> List.mapi (x.procAtom clauseNum) |>
                                List.filter (fun p -> p.IsSome) |> List.map Option.get |>  List.unzip
        let axioms = axioms |> List.concat
        
        // process rule
        let clauseName = "clause" + clauseNum.ToString()
        let atomsVars = atoms |> List.map x.CollectFreeVarsInAtom |> List.map (List.sort) |> List.filter (fun xs -> not (List.isEmpty xs))
        let clauseVars = x.CollectFreeVarsInAtoms atoms |> Set.ofList |> Set.toList |> List.sort
        let clauseVarsTerms = clauseVars |> List.map TIdent
        let clauseSorts = clauseVars |> List.map snd
        let clauseDecls, cRecord = x.generateAutomataDeclarations clauseName clauseSorts
        
        let clauseLen = List.length positions
        let prodName = "prod" + clauseLen.ToString()
        let stateVars = List.init clauseLen (fun _ -> (gensym(), stateSort))
        let stateTerms = stateVars |> List.map TIdent
        let prodOp =
            let ss = List.init clauseLen (fun _ -> stateSort)
            Operation.makeElementaryOperationFromSorts prodName ss stateSort
        
        // TODO: what if m > 1
        let initAxiom =
            let l = cRecord.initConst
            let inits = List.map (fun r -> r.initConst) positions
            let r = TApply(prodOp, inits)
            rule [] [] (AApply(equal_op stateSort, [l; r]))
        let deltaAxiom =
            let atomsTerms = List.map (List.map TIdent) atomsVars
            let rs = List.map3 (fun r vs s -> TApply(r.delta, vs @ [s]) ) positions atomsTerms stateTerms
            let r = TApply(prodOp, rs)
            let lState = TApply(prodOp, stateTerms)
            let l = TApply(cRecord.delta, clauseVarsTerms @ [lState])
            rule (stateVars @ clauseVars) [] (AApply(equal_op stateSort, [l; r]))
        let finalAxiom =
            let li = TApply(prodOp, stateTerms)
            let l = AApply(cRecord.isFinal, [li])
            let rs,lastR = positions |> List.splitAt (clauseLen - 1)
            let states, lastState = stateTerms |> List.splitAt (clauseLen - 1)
            let rs = List.map2 (fun r q -> AApply(r.isFinal, [q]) ) rs states 
            // head isFinal is negated
            let lastR = List.exactlyOne lastR
            let lastR =
                match head with
                | Bot ->
                    AApply(lastR.isFinal, lastState)
                | _ ->
                    AApply(notop, [TApply(lastR.isFinal, lastState)])
            eqRule stateVars (rs @ [lastR]) l
        let reachInit =
            rule [] [] (AApply(cRecord.reach, [cRecord.initConst]))
        let reachDelta =
            let qVar = ("q", stateSort)
            let qTerm = TIdent qVar
            let l = AApply(cRecord.reach, [qTerm])
            let ri = TApply(cRecord.delta, clauseVarsTerms @ [qTerm])
            let r = AApply(cRecord.reach, [ri])
            rule (clauseVars @ [qVar]) [l] r
        let condition =
            let qVar = ("q", stateSort)
            let qTerm = TIdent qVar               
            let l = AApply(cRecord.reach, [qTerm])
            let r = AApply(notop, [TApply(cRecord.isFinal, [qTerm])])
            rule [qVar] [l] r
        
        axioms @ clauseDecls @ List.map TransformedCommand [initAxiom; deltaAxiom; finalAxiom; reachInit; reachDelta; condition]
    
    member x.procRules rules =
        rules |> List.mapi x.procRule

    member x.declareProds maxArity =
        seq {
            for i in [1..maxArity] do
                let name = "prod" + i.ToString()
                let states = List.init i (fun _ -> stateSort)
                OriginalCommand (DeclareFun(name, states, stateSort))
        }
    member x.dumpCommands() =
        let processeedDts = x.parseDatatypes adts
        // TODO: remove constant
        let prods = x.declareProds 2
        Seq.append processeedDts prods

let transform commands =
    let commandParser = function
        | OriginalCommand o -> Choice1Of2 o
        | TransformedCommand t -> Choice2Of2 t
        | _ -> __unreachable__()
    let oCommands, tComands = List.choose2 commandParser commands
    let adt_decls, oCommands = oCommands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [(a, b)] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let processer = Processer(adt_decls)
    let oCommands = processer.processDeclarations oCommands
    // TODO: ltlt debug
    let pCommands = processer.procRules [tComands.[6]; tComands.[7]; tComands.[8]] |> List.concat
    let tCommands = processer.dumpCommands()
    let commands = Seq.append tCommands oCommands |> Seq.toList
    [OriginalCommand(DeclareSort(stateSort))] @ commands @ pCommands
