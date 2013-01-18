module CleanRegions

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp


let (|RegionDirective|_|) (expr:SyntaxTrivia) =    if expr.Kind = SyntaxKind.RegionDirectiveTrivia then Some(expr) else None
let (|EndRegionDirective|_|) (expr:SyntaxTrivia) = if expr.Kind = SyntaxKind.EndRegionDirectiveTrivia then Some(expr) else None
let (|EndOfLine|_|) (expr:SyntaxTrivia) =          if expr.Kind = SyntaxKind.EndOfLineTrivia then Some(expr) else None
let (|Whitespace|_|) (expr:SyntaxTrivia) =         if expr.Kind = SyntaxKind.WhitespaceTrivia then Some(expr) else None


type RegionRemover() = 
   inherit SyntaxRewriter(false)

   override x.VisitToken token =
      let rec removeRegions (list:SyntaxTrivia list) (node:SyntaxToken) =
         match list with
         | EndOfLine(t1)::Whitespace(t2)::RegionDirective(hd)::tl    -> 
            let newNode = node.ReplaceTrivia([t2; hd], System.Func<SyntaxTrivia, SyntaxTrivia, SyntaxTriviaList>(fun a1 a2 -> SyntaxTriviaList.Empty))
            removeRegions tl newNode
         | RegionDirective(hd)::tl                                   -> removeRegions tl (node.ReplaceTrivia(hd, SyntaxTriviaList.Empty))
         | EndOfLine(t1)::Whitespace(t2)::EndRegionDirective(hd)::tl -> 
            let newNode = node.ReplaceTrivia([t2; hd], System.Func<SyntaxTrivia, SyntaxTrivia, SyntaxTriviaList>(fun a1 a2 -> SyntaxTriviaList.Empty))
            removeRegions tl newNode
         | hd::tl                                                    -> removeRegions tl node
         | _                                                         -> node

      match (token.HasLeadingTrivia, token.HasTrailingTrivia) with
      | (true, true)   -> 
         let list1 = token.LeadingTrivia |> Seq.toList
         let list2 = token.TrailingTrivia |> Seq.toList
         let t2 = removeRegions (list1 @ list2) token
         t2
      | (true, false)  -> removeRegions (token.LeadingTrivia |> Seq.toList) token
      | (false, true)  -> removeRegions (token.TrailingTrivia |> Seq.toList) token
      | (false, false) -> base.VisitToken token


type MemberCollector() = 
   inherit SyntaxRewriter(false)

   let mutable constructors = List<ConstructorDeclarationSyntax>.Empty
   let mutable methods = List<MethodDeclarationSyntax>.Empty

   member x.Ctors
     with get() = if constructors.IsEmpty then None else 
                     let list = constructors |> List.sortBy (fun t -> t.ParameterList.ChildNodes().Count())
//                     Syntax.RegionDirectiveTrivia(true) :> SyntaxTrivia
                     //list.Head.Identifier.WithLeadingTrivia([].ToList())
                     //list.Head.WithIdentifier(
//                     if list.Head.AttributeLists.Count > 0 then
//                        list.Head.AttributeLists.First().OpenBracketToken
                     Some(Syntax.List(list |> List.map (fun t -> t :> MemberDeclarationSyntax)))

   member x.Methods with get() = if methods.IsEmpty      then None else Some(Syntax.List(methods |> List.sortBy (fun t -> t.Identifier.ValueText) |> List.map (fun t -> t :> MemberDeclarationSyntax)))

   override x.VisitConstructorDeclaration node = 
      constructors <- node :: constructors
      null

   override x.VisitMethodDeclaration node =
      methods <- node :: methods
      null


type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let extend ((node:ClassDeclarationSyntax), (members:SyntaxList<MemberDeclarationSyntax> option)) =
         match members with
         | Some(list) -> node.WithMembers(Syntax.List(list.Concat(node.Members)))
         | None       -> node

      ((node, collector.Methods) |> extend, collector.Ctors) |> extend :> SyntaxNode


let cleanRegions (root:CompilationUnitSyntax) =
   let collector = MemberCollector()
   let cleanRoot = root.Accept(RegionRemover()).Accept(collector)
   cleanRoot.Accept(RegionRewriter(collector))