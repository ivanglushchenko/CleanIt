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
   let mutable events = List<EventFieldDeclarationSyntax>.Empty
   let mutable fields = List<FieldDeclarationSyntax>.Empty
   let mutable methods = List<MethodDeclarationSyntax>.Empty
   let startTokens = System.Collections.Generic.HashSet<MemberDeclarationSyntax>()
   let endTokens = System.Collections.Generic.HashSet<MemberDeclarationSyntax>()

   let toSyntaxList list =
      let cnvList = list |> List.map (fun t -> t :> MemberDeclarationSyntax)
      ignore <| startTokens.Add (cnvList.First())
      ignore <| endTokens.Add (cnvList.Last())
      Some(Syntax.List(cnvList))

   member x.Ctors       with get() = if constructors.IsEmpty then None else toSyntaxList(constructors |> List.sortBy (fun t -> t.ParameterList.ChildNodes().Count()))
   member x.Events      with get() = if events.IsEmpty       then None else toSyntaxList(events |> List.sortBy (fun t -> t.Declaration.Variables.First().Identifier.ValueText))
   member x.Fields      with get() = if fields.IsEmpty       then None else toSyntaxList(fields |> List.sortBy (fun t -> t.Declaration.Variables.First().Identifier.ValueText))
   member x.Methods     with get() = if methods.IsEmpty      then None else toSyntaxList(methods |> List.sortBy (fun t -> t.Identifier.ValueText))
   member x.StartTokens with get() = startTokens
   member x.EndTokens   with get() = endTokens

   override x.VisitConstructorDeclaration node = 
      constructors <- node :: constructors
      null

   override x.VisitEventFieldDeclaration node =
      events <- node :: events
      null

   override x.VisitFieldDeclaration node =
      fields <- node :: fields
      null

   override x.VisitMethodDeclaration node =
      methods <- node :: methods
      null


type MemberArranger(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let extend (members:SyntaxList<MemberDeclarationSyntax> option) (node:ClassDeclarationSyntax) =
         match members with
         | Some(list) -> node.WithMembers(Syntax.List(list.Concat(node.Members)))
         | None       -> node
      
      base.VisitClassDeclaration (node |> extend collector.Methods |> extend collector.Fields |> extend collector.Events |> extend collector.Ctors)


type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   let mutable ctorsRegionOpened = false
   let mutable ctorsRegionClosed = false
   let mutable eventsRegionOpened = false
   let mutable eventsRegionClosed = false
   let mutable fieldsRegionOpened = false
   let mutable fieldsRegionClosed = false
   let mutable methodsRegionOpened = false
   let mutable methodsRegionClosed = false

   let addRegionOpenOrClose (isOpen:bool) (token:SyntaxToken) (name:string) =
      let rec removeDoubleEndlines list =
         match list with
         | EndOfLine(t1) :: EndOfLine(t2) :: tl -> removeDoubleEndlines (t2 :: tl)
         | hd :: tl                             -> hd :: removeDoubleEndlines tl
         | _                                    -> []
      let formattedList = removeDoubleEndlines (token.LeadingTrivia |> Seq.toList)
      let regionList = (SyntaxTree.ParseText ((if isOpen then "#region " else "#endregion ") + name)).GetRoot().GetLeadingTrivia() |> Seq.toList
      match formattedList with
      | EndOfLine(t1) :: Whitespace(t2) :: tl -> 
         let trivia = [Syntax.EndOfLine(t1.ToFullString()); Syntax.Whitespace(t2.ToFullString())] @ regionList @ (if isOpen = false then [Syntax.EndOfLine(t1.ToFullString())] else []) @ [Syntax.EndOfLine(t1.ToFullString()); t1; t2] @ tl
         token.WithLeadingTrivia(trivia)
      | Whitespace(t1) :: tl -> token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString())] @ regionList @ [Syntax.EndOfLine("\r\n", true)] @ formattedList)
      | _ -> token.WithLeadingTrivia(regionList @ formattedList)

   let openRegion = addRegionOpenOrClose true
   let closeRegion = addRegionOpenOrClose false

   override x.VisitToken token =
      match (token.Parent, ctorsRegionOpened, eventsRegionOpened, fieldsRegionOpened, methodsRegionOpened) with
      | (:? ConstructorDeclarationSyntax, false,     _,     _,     _) -> 
         ctorsRegionOpened <- true
         openRegion token ".ctors"
      | (:? EventFieldDeclarationSyntax,   true, false,     _,     _) ->
         eventsRegionOpened <- true
         ctorsRegionClosed <- true
         closeRegion (openRegion token "Events") ".ctors"
      | (:? EventFieldDeclarationSyntax,      _, false,     _,     _) ->
         eventsRegionOpened <- true
         openRegion token "Events"
      | (:? FieldDeclarationSyntax,        true, false, false,     _) ->
         fieldsRegionOpened <- true
         closeRegion (openRegion token "Fields") ".ctors"
      | (:? FieldDeclarationSyntax,           _,  true, false,     _) ->
         fieldsRegionOpened <- true
         closeRegion (openRegion token "Fields") "Events"
      | (:? FieldDeclarationSyntax,           _,     _, false,     _) ->
         fieldsRegionOpened <- true
         openRegion token "Fields"
      | (:? MethodDeclarationSyntax,       true, false, false, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") ".ctors"
      | (:? MethodDeclarationSyntax,          _,   true, false, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") "Events"
      | (:? MethodDeclarationSyntax,          _,      _,  true, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") "Fields"
      | (:? MethodDeclarationSyntax,          _,     _,     _, false) ->
         methodsRegionOpened <- true
         openRegion token "Methods"
      | (:? ClassDeclarationSyntax,        true, false, false, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token ".ctors"
      | (:? ClassDeclarationSyntax,           _,  true, false, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Events"
      | (:? ClassDeclarationSyntax,           _,     _,  true, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Fields"
      | (:? ClassDeclarationSyntax,           _,     _,     _, true)  when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Methods"
      | _ -> base.VisitToken token


type FormatHelper() =
   inherit SyntaxRewriter(false)

   override x.VisitToken token =
      match token.Kind with
      | SyntaxKind.SemicolonToken -> 
         match token.GetPreviousToken().Kind with
         | SyntaxKind.CloseBraceToken | SyntaxKind.CloseParenToken -> token.WithLeadingTrivia().WithTrailingTrivia(Syntax.ElasticCarriageReturnLineFeed)
         | _ -> token
      | SyntaxKind.CloseBraceToken ->
         match token.GetNextToken().Kind with
         | SyntaxKind.CloseParenToken | SyntaxKind.SemicolonToken -> token.WithTrailingTrivia()
         | _ -> token
      | SyntaxKind.CloseParenToken ->
         if token.GetPreviousToken().Kind = SyntaxKind.CloseBraceToken then token.WithLeadingTrivia() else token
      | _ -> token


let cleanRegions (root:CompilationUnitSyntax) =
   let collector = MemberCollector()
   let cleanRoot = root.Accept(RegionRemover()).Accept(collector)
   cleanRoot.Accept(MemberArranger(collector)).Accept(RegionRewriter(collector))

//var formattedCode = new CodeBeautifier().Visit(root.Format()).GetFullText();
   