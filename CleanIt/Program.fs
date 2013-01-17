module CleanIt.Program

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp
open CleanIt.UsingDirectiveRewrite

let rec printNode (node:SyntaxNode) level =
   let prepend (s : string) minLength = 
      sprintf "%s%s" (new System.String(' ', if s.Length >= minLength then 0 else minLength - s.Length)) s
   let postpend (s : string) minLength = 
      sprintf "%s%s" s (new System.String(' ', if s.Length >= minLength then 0 else minLength - s.Length))

   let nodeText = node.GetText()
   let text = postpend (sprintf "%s%A %s" (new System.String(' ', level * 2))  node.Kind (node.GetType().Name)) 75
   printf "%s %s\n" text (sprintf "%s %s" (prepend (sprintf "[%i]" (nodeText.LineCount)) 6) (nodeText.Lines.First().ToString()))
   node.ChildNodes() |> Seq.iter(fun c -> printNode c (level+1))


let (|UsingDirective|_|) (expr:SyntaxNode) = 
    match expr with 
    | :? UsingDirectiveSyntax as expr -> Some(expr)
    | _ -> None


let (|QualifiedName|_|) (expr:SyntaxNode) = 
    match expr with 
    | :? QualifiedNameSyntax as expr -> Some(expr)
    | _ -> None


let cleanFile fileName = 
    printfn "processing file \"%s\"\n" fileName
    let code = (new System.IO.StreamReader(fileName)).ReadToEnd()
    let ast = SyntaxTree.ParseText code
    let root = ast.GetRoot()
    let rewriter = UsingDirectiveRewrite()
    let rootAlt = root.Accept(rewriter) :?> CompilationUnitSyntax
    let usings = rewriter.getCollectedUsings()
    let rewrittenRoot = rootAlt.AddUsings usings
    printNode rewrittenRoot 0
    let writer = new System.IO.StreamWriter(fileName)
    rewrittenRoot.WriteTo(writer)
    writer.Flush()
    writer.Close()

[<EntryPoint>]
let main argv = 
    cleanFile "c:\Temp\App.cs"
    System.Console.ReadLine() |> ignore
    0 // return an integer exit code

