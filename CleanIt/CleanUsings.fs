module CleanUsings

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp

type UsingDirectiveRewrite() = 
   inherit SyntaxRewriter(false)

   let usings = System.Collections.Generic.List<UsingDirectiveSyntax>()

   member visitor.getCollectedUsings() = usings |> Seq.sortBy (fun (t:UsingDirectiveSyntax) -> t.ToString().TrimEnd(';')) |> Seq.toArray

   override visitor.VisitUsingDirective node =
      if node.UsingKeyword.HasLeadingTrivia then
         let rec cleanUpTrivia (l: SyntaxTrivia list) =
            match l with
            | hd :: nk :: tl when hd.Kind = SyntaxKind.SingleLineCommentTrivia && nk.Kind = SyntaxKind.EndOfLineTrivia -> hd :: nk :: cleanUpTrivia tl
            | hd :: tl when hd.Kind = SyntaxKind.EndOfLineTrivia -> cleanUpTrivia tl
            | hd :: tl -> hd :: cleanUpTrivia tl
            | [] -> []
         let niceUsingToken = node.UsingKeyword.WithLeadingTrivia(cleanUpTrivia (node.UsingKeyword.LeadingTrivia |> Seq.toList))
         let niceUsing = node.WithUsingKeyword niceUsingToken
         usings.Add niceUsing
      else
         usings.Add node
      
      null
   
let cleanUsings (root:CompilationUnitSyntax) =
   let rewriter = UsingDirectiveRewrite()
   let nodeWithNoUsings = root.Accept(rewriter) :?> CompilationUnitSyntax
   let usings = rewriter.getCollectedUsings()
   nodeWithNoUsings.AddUsings usings
