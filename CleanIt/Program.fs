module CleanIt.Program

open System.IO
open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp
open CleanUsings
open CleanRegions

let rec printNode (node:SyntaxNode) level =
   let prepend (s : string) minLength = 
      sprintf "%s%s" (new System.String(' ', if s.Length >= minLength then 0 else minLength - s.Length)) s
   let postpend (s : string) minLength = 
      sprintf "%s%s" s (new System.String(' ', if s.Length >= minLength then 0 else minLength - s.Length))

   let nodeText = node.GetText()
   let text = postpend (sprintf "%s%A %s" (new System.String(' ', level * 2))  node.Kind (node.GetType().Name)) 75
   let rec getFirstNonEmptyLine (t:ITextLine list) =
      match t with
      | hd::tl ->
         let s = hd.ToString().Trim('\n', '\r')
         if System.String.IsNullOrWhiteSpace(s) then getFirstNonEmptyLine tl else s
      | hd -> hd.ToString()

   printf "%s %s\n" text (sprintf "%s %s" (prepend (sprintf "[%i]" (nodeText.LineCount)) 6) ((getFirstNonEmptyLine (nodeText.Lines |> Seq.toList))))
   node.ChildNodes() |> Seq.iter(fun c -> printNode c (level+1))


let cleanFile fileName = 
    printfn "processing file \"%s\"\n" fileName
    let stream = new FileStream(fileName, FileMode.Open, FileAccess.Read)
    let code = (new System.IO.StreamReader(stream)).ReadToEnd()
    stream.Dispose()
    stream.Close()
    let ast = SyntaxTree.ParseText code
    let root = ast.GetRoot()
    let rewrittenRoot =  root |> cleanUsings |> cleanRegions

    //printNode rewrittenRoot 0
    let writer = new System.IO.StreamWriter(fileName + ".proc")
    rewrittenRoot.WriteTo(writer)
    writer.Flush()
    writer.Close()


[<EntryPoint>]
let main argv = 
    cleanFile "TestCode.txt"//"c:\Temp\App2.cs"
    //System.Console.ReadLine() |> ignore
    0 // return an integer exit code

