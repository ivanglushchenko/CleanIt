module CleanIt.UsingDirectiveRewrite

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp

type UsingDirectiveRewrite() = 
   inherit SyntaxRewriter(false)

   let collect = true
   let usings = System.Collections.Generic.List<UsingDirectiveSyntax>()

   member visitor.getCollectedUsings() = usings |> Seq.sortBy (fun (t:UsingDirectiveSyntax) -> t.ToString()) |> Seq.toArray

   override visitor.VisitUsingDirective node =
      if node.UsingKeyword.HasLeadingTrivia then
         let niceUsingToken = node.UsingKeyword.WithLeadingTrivia()
         let niceUsing = node.WithUsingKeyword niceUsingToken
         usings.Add niceUsing
      else
         usings.Add node
      
      null
   