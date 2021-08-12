module RInGen.Transformers
open System
open System.IO
open Programs

type TransformationFail = TRANS_TIMELIMIT | TRANS_HIGH_ORDER_PROBLEM | TRANS_CONTAINS_EXISTENTIALS | TRANS_UNHANDLED_EXCEPTION

let tryParseTransformationFail (s : string) =
    let s = s.Trim()
    match s with
    | "TRANS_TIMELIMIT" -> Some TRANS_TIMELIMIT
    | "TRANS_HIGH_ORDER_PROBLEM" -> Some TRANS_HIGH_ORDER_PROBLEM
    | "TRANS_CONTAINS_EXISTENTIALS" -> Some TRANS_CONTAINS_EXISTENTIALS
    | "TRANS_UNHANDLED_EXCEPTION" -> Some TRANS_UNHANDLED_EXCEPTION
    | _ -> None

[<AbstractClass>]
type TransformerProgram (options) =
    inherit Program()

    let isHighOrderBenchmark cmnds =
        let hasDefines = List.exists (function Definition _ -> true | _ -> false) cmnds
        let hasDeclareFuns = List.exists (function Command (DeclareFun _) -> true | _ -> false) cmnds
        hasDefines && hasDeclareFuns

    let tryFindExistentialClauses =
        let rec tryFindExistentialClauses = function
            | BaseRule _ -> None
            | ExistsRule _ as r -> Some r
            | ForallRule(_, r) -> tryFindExistentialClauses r
        let tryFindExistentialClauses = function
            | TransformedCommand r -> tryFindExistentialClauses r
            | _ -> None
        List.tryPick tryFindExistentialClauses

    abstract Transform : transformedCommand list -> transformedCommand list
    abstract CommandsToStrings : transformedCommand list -> string list
    default x.CommandsToStrings commands = List.map toString commands

    static member FailInfoFileExtension = ".transformation_info"

    member private x.ReportTransformationProblem dstPath (problem : TransformationFail) message =
        let dstPath = Path.ChangeExtension(dstPath, TransformerProgram.FailInfoFileExtension)
        File.WriteAllText(dstPath, toString problem)
        print_warn_verbose message

    member private x.SaveClauses dst commands =
        let lines = x.CommandsToStrings commands
        match tryFindExistentialClauses commands with
        | Some r -> x.ReportTransformationProblem dst TRANS_CONTAINS_EXISTENTIALS $"Transformed %s{dst} contains existential subclause: %O{r}"
        | _ -> x.SaveFile dst lines

    member private x.PerformTransform srcPath dstPath =
//        let mutable files = 0
//        let mutable successful = 0
//        let mutable total_generated = 0
//                files <- files + 1
        let exprs = SMTExpr.parseFile srcPath
        if isHighOrderBenchmark exprs then x.ReportTransformationProblem dstPath TRANS_HIGH_ORDER_PROBLEM $"%s{srcPath} will not be transformed as it has a mix of define-fun and declare-fun commands" else
        try
            let originalProgram = ClauseTransform.toClauses options exprs
            let transformedProgram = x.Transform originalProgram
            x.SaveClauses dstPath transformedProgram
//            total_generated <- total_generated + x.SaveClauses opts.path dst newTests
//            successful <- successful + 1
        with e -> x.ReportTransformationProblem dstPath TRANS_UNHANDLED_EXCEPTION $"Exception in %s{srcPath}: {e.Message}"
//        if IN_VERBOSE_MODE () then printfn $"All files:       %d{files}"
//        if IN_VERBOSE_MODE () then printfn $"Successful:      %d{successful}"
//        if IN_VERBOSE_MODE () then printfn $"Total generated: %d{total_generated}"

    override x.RunOnFile srcPath dstPath =
        print_verbose $"Transforming: %s{srcPath}"

        let task = Async.AwaitTask(Async.StartAsTask(async { x.PerformTransform srcPath dstPath }), MSECONDS_TIMEOUT ()) //TODO transformation time should count in total run
        match Async.RunSynchronously task with
        | Some () -> true
        | None -> x.ReportTransformationProblem dstPath TRANS_TIMELIMIT $"Transformation of %s{srcPath} halted due to a timelimit"; false

let private preambulizeCommands logic chcSystem =
    OriginalCommand(SetLogic logic) :: chcSystem @ [OriginalCommand CheckSat]

type OriginalTransformerProgram (options) =
    inherit TransformerProgram(options)

    override x.TargetPath path = $"%s{path}.Original"

    override x.Transform commands =
        preambulizeCommands "HORN" commands

type FreeSortsTransformerProgram (options) =
    inherit TransformerProgram(options)

    override x.TargetPath path = $"%s{path}.FreeSorts"

    override x.Transform commands =
        let noADTSystem = ClauseTransform.DatatypesToSorts.datatypesToSorts commands
        preambulizeCommands "UF" noADTSystem

type PrologTransformerProgram (options) =
    inherit OriginalTransformerProgram(options)

    override x.TargetPath path = $"%s{path}.Prolog"

    override x.FileExtension = ".pl"

    override x.CommandsToStrings commands =
        if PrintToProlog.isFirstOrderPrologProgram commands
            then PrintToProlog.toPrologFile commands
            else failwith_verbose $"not a first order Prolog program"
