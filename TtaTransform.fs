module RInGen.TtaTransform

open System
open System.Collections.Generic
open System.Linq.Expressions
open Antlr4.Runtime.Tree.Xpath
open Microsoft.FSharp.Collections
open RInGen

open RInGen.Prelude
open RInGen.IdentGenerator
open RInGen.Operations

let stateSort = gensymp "State" |> PrimitiveSort

type pattern = Pattern of string * term list

type AutomataRecord =
    { initConst : term
      isFinal : operation
      delta : operation
      reach: operation }

type Processer(adts) =
    // TODO: optimization
    let m = adts |> List.map snd |> List.concat |> List.map snd |> List.map (List.length) |> List.max
    let posDict = Dictionary()
    member x.getEqRelName s =
        "eq" + s.ToString()
    member x.getDiseqRelName s =
        "diseq" + s.ToString()

    member x.generateAutomataDeclarations name sortList =
        let initStatePrefix = "init_"
        let isFinalPrefix = "isFinal_"
        let deltaPrefix = "delta_"
        let reachPrefix = "reach_"
        
        let initStateName = initStatePrefix + name
        let isFinalName = isFinalPrefix + name
        let deltaName = deltaPrefix + name
        let reachName = reachPrefix + name

        let initStateDecl = DeclareConst (initStateName, stateSort)
        let isFinalDecl = DeclareFun(isFinalName, [stateSort], boolSort)
        let deltaDecl = DeclareFun(deltaName, sortList @ [stateSort], stateSort)
        let reachDecl = DeclareFun(reachName, [stateSort], boolSort)
        
        let initState = TConst(initStateName, stateSort)
        let isFinal = Operation.makeElementaryRelationFromSorts isFinalName [stateSort]
        let mStatesVec = List.init m (fun _ -> stateSort)
        let delta = Operation.makeElementaryOperationFromSorts deltaName (sortList @ mStatesVec) stateSort
        let reach = Operation.makeElementaryRelationFromSorts reachName [stateSort]

        // 1st - declarations to be added to commands
        // 2nd - operations to be used in new rules
        let aRec = {initConst = initState; isFinal = isFinal; delta = delta; reach=reach}
        List.map OriginalCommand [initStateDecl; isFinalDecl; deltaDecl; reachDecl], aRec

    member x.processDeclarations oCommands =
        let f el =
            match el with
            | DeclareFun(fname, args, res) ->
                let decls, aRec = x.generateAutomataDeclarations fname args
                let p = Pattern(fname, [])
                posDict.Add(p, aRec)
                Some decls
            | _ -> None

        let xs = oCommands |> List.map f |> List.filter (fun x -> x.IsSome)

        seq {
            for el in xs do
                match el with
                | Some c -> yield! c
                | None -> ()
        }

    member x.parseDatatypes adts =
        let processDt(s, xs) =
            let ys = List.map (fun x -> DeclareConst (fst x, s)) xs
            let bot = DeclareConst(s.getBotSymbol(), s)

            // eq axioms
            let eqRelName = x.getEqRelName s
            let decls, eqRec = x.generateAutomataDeclarations eqRelName [s; s]

            let initAtom = AApply(eqRec.isFinal, [eqRec.initConst])
            let initAxiom = TransformedCommand (rule [] [] initAtom)

            let q = TIdent(gensymp "q", stateSort)
            let f, g = TIdent(gensymp "f", s), TIdent(gensymp "g", s)
            let delta = TApply(eqRec.delta, [f; g; q])
            let l = AApply(eqRec.isFinal, [delta])
            let r = [AApply(equal_op s, [f; g]); AApply(eqRec.isFinal, [q])]
            let forallVars = [f; g; q] |> List.map (function TIdent(n, s) -> (n, s) ) // TODO: incomplete pattern matching
            let forallQuant = ForallQuantifier(forallVars)
            let deltaAxiom = TransformedCommand (Equivalence([forallQuant], r, l))
            
            // TODO: diseqAxioms ??
            // Note : diseq decls are generated twice, see parseDeclarations
            // let diseqRelName = x.getDiseqRelName s
            // let diseqDecls, diseqRec = x.generateAutomataDeclarations diseqRelName [s; s]
            // let deltaLeft = TApply(diseqRec.delta, [])
            // let deltaRight = TApply(eqRec.delta, [])
            // let deltaDiseqAtom = AApply(equal_op stateSort, [deltaLeft; deltaRight])

            List.map OriginalCommand ([DeclareSort(s); bot] @ ys) @
                decls @ [initAxiom; deltaAxiom]

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
       | AApply(op, ts) -> x.CollectFreeVarsInTerms ts
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
            let rs = List.map2 (fun r q -> AApply(r.isFinal, [q]) ) positions stateTerms 
            eqRule stateVars rs l
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
            let r = AApply(cRecord.isFinal, [qTerm])
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
    let oCommands, tComands = List.choose2 (function OriginalCommand o -> Choice1Of2 o | TransformedCommand t -> Choice2Of2 t) commands
    let adt_decls, oCommands = oCommands |> List.choose2 (function DeclareDatatype(a, b) -> Choice1Of2 [(a, b)] | DeclareDatatypes dts -> Choice1Of2 dts | c -> Choice2Of2 c)
    let adt_decls = List.concat adt_decls
    let processer = Processer(adt_decls)
    let oCommands = processer.processDeclarations oCommands
    let pCommands = processer.procRules [tComands.[6]; tComands.[7]; tComands.[8]] |> List.concat
    let tCommands = processer.dumpCommands()
    let commands = Seq.append tCommands oCommands |> Seq.toList
    [OriginalCommand(DeclareSort(stateSort))] @ commands @ pCommands
