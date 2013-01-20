module CleanRegions

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp
open Roslyn.Services.Formatting


let (|RegionDirective|_|) (expr:SyntaxTrivia) =    if expr.Kind = SyntaxKind.RegionDirectiveTrivia then Some(expr) else None
let (|EndRegionDirective|_|) (expr:SyntaxTrivia) = if expr.Kind = SyntaxKind.EndRegionDirectiveTrivia then Some(expr) else None
let (|EndOfLine|_|) (expr:SyntaxTrivia) =          if expr.Kind = SyntaxKind.EndOfLineTrivia then Some(expr) else None
let (|Whitespace|_|) (expr:SyntaxTrivia) =         if expr.Kind = SyntaxKind.WhitespaceTrivia then Some(expr) else None

let eol() = Syntax.EndOfLine("\r\n", false)
let tab() = Syntax.Whitespace("\t", false)


type Construct =
    | DependencyProperty of string * FieldDeclarationSyntax * PropertyDeclarationSyntax
    | Property of string * FieldDeclarationSyntax * PropertyDeclarationSyntax
    
let getConstructName = function
   | DependencyProperty(name, _, _) -> name
   | Property(name, _, _)           -> name

let getConstructNodes = function
   | DependencyProperty(name, f, p) -> [f :> MemberDeclarationSyntax; p :> MemberDeclarationSyntax]
   | Property(name, f, p)           -> [f :> MemberDeclarationSyntax; p :> MemberDeclarationSyntax]


type Member =
   | Ctor
   | Event
   | Field
   | Property
   | Method
   | Other


type RegionRemover() = 
   inherit SyntaxRewriter(false)

   override x.VisitToken token =
      let rec removeRegions (list:SyntaxTrivia list) =
         match list with
         | EndOfLine(t1) :: Whitespace(t2) :: RegionDirective(hd) :: tl    -> removeRegions (t1 :: tl)
         | RegionDirective(hd) :: tl                                       -> removeRegions tl
         | EndOfLine(t1) :: Whitespace(t2) :: EndRegionDirective(hd) :: tl -> removeRegions (t1 :: tl)
         | EndRegionDirective(hd) :: tl                                    -> removeRegions tl
         | EndOfLine(t1) :: EndOfLine(t2) :: tl                            -> removeRegions (t2 :: tl)
         | hd::tl                                                          -> hd :: removeRegions tl
         | _                                                               -> []

      match (token.HasLeadingTrivia, token.HasTrailingTrivia) with
      | (true, true)   -> token.WithLeadingTrivia(removeRegions (token.LeadingTrivia |> Seq.toList)).WithTrailingTrivia(removeRegions (token.TrailingTrivia |> Seq.toList))
      | (true, false)  -> token.WithLeadingTrivia(removeRegions (token.LeadingTrivia |> Seq.toList))
      | (false, true)  -> token.WithTrailingTrivia(removeRegions (token.TrailingTrivia |> Seq.toList))
      | (false, false) -> base.VisitToken token


type MemberCollector() = 
   inherit SyntaxRewriter(false)

   let join (s:string seq) = 
      let l = s.ToArray()
      if l.Length = 0 then ""
      else " " + System.String.Join(":", l)

   let getSignature (pSyntax:ParameterListSyntax) = join (pSyntax.Parameters |> Seq.map (fun t -> t.Type.ToString()))
   let getModifiers (tokens:SyntaxTokenList) = join (tokens |> Seq.map (fun t -> t.ValueText))

   let isStatic (tokens:SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "static")
   let isPublic (tokens:SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "public")

   let mutable constructs = Map.empty<string, Construct>
   let mutable constructors = Map.empty<string, ConstructorDeclarationSyntax>
   let mutable events = Map.empty<string, EventFieldDeclarationSyntax>
   let mutable fields = Map.empty<string, FieldDeclarationSyntax>
   let mutable properties = Map.empty<string, PropertyDeclarationSyntax>
   let mutable methods = Map.empty<string, MethodDeclarationSyntax>

   let toSyntaxList (map:Map<string, #MemberDeclarationSyntax>) regionType = 
      if map.IsEmpty = true then None
      else Some(Syntax.List(map |> Map.toList |> List.map (fun (t1, t2) -> t2 :> MemberDeclarationSyntax)))

   let collectConstructs name =
      let dpPropName = name + "Property"
      if fields.ContainsKey(dpPropName) && properties.ContainsKey(name) then
         let fNode = fields.[dpPropName]
         let pNode = properties.[name]
         if (isStatic fNode.Modifiers) && fNode.Declaration.Type.ToString() = "DependencyProperty" then
            let c = DependencyProperty(name, fNode, pNode)
            constructs <- constructs.Add (name, c)
            fields <- fields.Remove(dpPropName)
            properties <- properties.Remove(name)


   member x.Ctors       with get() = toSyntaxList constructors Ctor
   member x.Events      with get() = toSyntaxList events Event
   member x.Fields      with get() = toSyntaxList fields Field
   member x.Properties  with get() = toSyntaxList properties Property
   member x.Methods     with get() = toSyntaxList methods Method
   member x.Constructs  with get() = if constructs.IsEmpty   then None else Some(Syntax.List(constructs |> Map.toList |> List.collect (fun (t1, t2) -> getConstructNodes t2)))

   override x.VisitConstructorDeclaration node = 
      constructors <- constructors.Add (node.ParameterList.ChildNodes().Count().ToString() + getModifiers(node.Modifiers), node)
      null

   override x.VisitEventFieldDeclaration node =
      events <- events.Add (node.Declaration.Variables.First().Identifier.ValueText, node)
      null

   override x.VisitFieldDeclaration node =
      let name = node.Declaration.Variables.First().Identifier.ValueText
      fields <- fields.Add (name, node)
      collectConstructs (if name.EndsWith "Property" then name.Substring(0, name.Length - 8) else name)
      null

   override x.VisitPropertyDeclaration node =
      properties <- properties.Add (node.Identifier.ValueText, node)
      collectConstructs node.Identifier.ValueText
      null

   override x.VisitMethodDeclaration node =
      methods <- methods.Add (node.Identifier.ValueText + getSignature(node.ParameterList), node)
      null


type MemberArranger(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let extend (members:SyntaxList<MemberDeclarationSyntax> option) (node:ClassDeclarationSyntax) =
         match members with
         | Some(list) -> node.WithMembers(Syntax.List(list.Concat(node.Members)))
         | None       -> node
      base.VisitClassDeclaration (node |> extend collector.Methods |> extend collector.Properties |> extend collector.Constructs |> extend collector.Fields |> extend collector.Events |> extend collector.Ctors)


type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   let mutable ctorsRegionOpened = false
   let mutable eventsRegionOpened = false
   let mutable fieldsRegionOpened = false
   let mutable propertiesRegionOpened = false
   let mutable methodsRegionOpened = false

   let addRegionOpenOrClose (isOpen:bool) (token:SyntaxToken) (name:string) =
      let formattedList = (token.LeadingTrivia |> Seq.toList)
      let region = if isOpen then SyntaxTree.ParseText("#region " + name).GetRoot().GetLeadingTrivia().First() else Syntax.Trivia(Syntax.EndRegionDirectiveTrivia(true))
      match formattedList with
      | EndOfLine(t1) :: Whitespace(t2) :: tl -> 
         let trivia = [eol(); tab(); region; eol(); eol(); t2] @ tl
         token.WithLeadingTrivia(trivia)
      | Whitespace(t1) :: tl -> token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString()); tab(); region] @ [eol(); eol()] @ formattedList)
      | _ -> token.WithLeadingTrivia(eol() :: tab() :: region :: formattedList)

   let openRegion = addRegionOpenOrClose true
   let closeRegion = addRegionOpenOrClose false

   override x.VisitToken token =
      match (token.Parent, ctorsRegionOpened, eventsRegionOpened, fieldsRegionOpened, propertiesRegionOpened, methodsRegionOpened) with
      | (:? ConstructorDeclarationSyntax, false,     _,     _,     _,     _) -> 
         ctorsRegionOpened <- true
         openRegion token ".ctors"
      | (:? EventFieldDeclarationSyntax,   true, false,     _,     _,     _) ->
         eventsRegionOpened <- true
         closeRegion (openRegion token "Events") ".ctors"
      | (:? EventFieldDeclarationSyntax,      _, false,     _,     _,     _) ->
         eventsRegionOpened <- true
         openRegion token "Events"
      | (:? FieldDeclarationSyntax,        true, false, false,     _,     _) ->
         fieldsRegionOpened <- true
         closeRegion (openRegion token "Fields") ".ctors"
      | (:? FieldDeclarationSyntax,           _,  true, false,     _,     _) ->
         fieldsRegionOpened <- true
         closeRegion (openRegion token "Fields") "Events"
      | (:? FieldDeclarationSyntax,           _,     _, false,     _,     _) ->
         fieldsRegionOpened <- true
         openRegion token "Fields"
      | (:? PropertyDeclarationSyntax,     true, false, false, false,     _) ->
         propertiesRegionOpened <- true                                      
         closeRegion (openRegion token "Properties") ".ctors"             
      | (:? PropertyDeclarationSyntax,        _,  true, false, false,     _) ->
         propertiesRegionOpened <- true                                      
         closeRegion (openRegion token "Properties") "Events"             
      | (:? PropertyDeclarationSyntax,        _,     _,  true, false,     _) ->
         propertiesRegionOpened <- true                                      
         closeRegion (openRegion token "Properties") "Fields"             
      | (:? PropertyDeclarationSyntax,        _,     _,     _, false,     _) ->
         propertiesRegionOpened <- true
         openRegion token "Properties"
      | (:? MethodDeclarationSyntax,       true, false, false, false, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") ".ctors"
      | (:? MethodDeclarationSyntax,          _,  true, false, false, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") "Events"
      | (:? MethodDeclarationSyntax,          _,     _,  true, false, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") "Fields"
      | (:? MethodDeclarationSyntax,          _,     _,     _,  true, false) ->
         methodsRegionOpened <- true
         closeRegion (openRegion token "Methods") "Properties"
      | (:? MethodDeclarationSyntax,          _,     _,     _,     _, false) ->
         methodsRegionOpened <- true
         openRegion token "Methods"
      | (:? ClassDeclarationSyntax,        true, false, false, false, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token ".ctors"
      | (:? ClassDeclarationSyntax,           _,  true, false, false, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Events"
      | (:? ClassDeclarationSyntax,           _,     _,  true, false, false) when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Fields"
      | (:? ClassDeclarationSyntax,           _,     _,     _,  true, false)  when token.Kind = SyntaxKind.CloseBraceToken ->
         closeRegion token "Properties"
      | (:? ClassDeclarationSyntax,           _,     _,     _,     _,  true)  when token.Kind = SyntaxKind.CloseBraceToken ->
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
   let fmtOptions = FormattingOptions(false, 4, 4)
   let fmtHelper = FormatHelper()
   cleanRoot.Accept(MemberArranger(collector)).Accept(RegionRewriter(collector))//.Format(fmtOptions).GetFormattedRoot() :?> SyntaxNode |> fmtHelper.Visit

//var formattedCode = new CodeBeautifier().Visit(root.Format()).GetFullText();
   