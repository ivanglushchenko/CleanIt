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


type RegionType =
   | Ctors
   | Events
   | Fields
   | Properties
   | Methods
   | Other

let getName = function
   | Ctors      -> ".ctors"
   | Events     -> "Events"
   | Fields     -> "Fields"
   | Properties -> "Properties"
   | Methods    -> "Methods"
   | Other      -> "Other"

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

   let getSignature (pSyntax: ParameterListSyntax) = join (pSyntax.Parameters |> Seq.map (fun t -> t.Type.ToString()))
   let getModifiers (tokens: SyntaxTokenList) = join (tokens |> Seq.map (fun t -> t.ValueText))

   let isStatic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "static")
   let isPublic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "public")

   let mutable constructs = Map.empty<string, Construct>
   let mutable constructors = Map.empty<string, ConstructorDeclarationSyntax>
   let mutable events = Map.empty<string, EventFieldDeclarationSyntax>
   let mutable fields = Map.empty<string, FieldDeclarationSyntax>
   let mutable properties = Map.empty<string, PropertyDeclarationSyntax>
   let mutable methods = Map.empty<string, MethodDeclarationSyntax>

   let mutable openRegionMarkers = Map.empty<string, RegionType>

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

   let toSyntaxList (map:Map<string, #MemberDeclarationSyntax>) = 
      if map.IsEmpty = true then None
      else Some(Syntax.List(map |> Map.toList |> List.map (fun (t1, t2) -> t2 :> MemberDeclarationSyntax)))

   let markRegionBorders regionType (tokens: SyntaxList<MemberDeclarationSyntax> option) =
      match tokens with
      | Some(l) -> 
         let first = l.First()
         let token = first.ToString()
         openRegionMarkers <- openRegionMarkers.Add (token, regionType)
         Some(l)
      | None -> None

   member x.Ctors             with get() = toSyntaxList constructors |> markRegionBorders Ctors
   member x.Events            with get() = toSyntaxList events |> markRegionBorders Events
   member x.Fields            with get() = toSyntaxList fields |> markRegionBorders Fields
   member x.Properties        with get() = 
                                 let p = properties |> Map.toList |> List.map (fun (t1, t2) -> t2 :> MemberDeclarationSyntax)
                                 let c = constructs |> Map.toList |> List.collect (fun (t1, t2) -> getConstructNodes t2)
                                 let fullList = c @ p
                                 if fullList.IsEmpty then None else Some(Syntax.List(fullList)) |> markRegionBorders Properties
   member x.Methods           with get() = toSyntaxList methods |> markRegionBorders Methods
   member x.OpenRegionMarkers with get() = openRegionMarkers

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
      base.VisitClassDeclaration (node |> extend collector.Methods |> extend collector.Properties |> extend collector.Fields |> extend collector.Events |> extend collector.Ctors)


type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   let mutable openedRegions = Set.empty<RegionType>
   let mutable closedRegions = Set.empty<RegionType>

   let addRegion (token: SyntaxToken) (region: SyntaxTrivia) =
      let formattedList = (token.LeadingTrivia |> Seq.toList)
      match formattedList with
      | EndOfLine(t1) :: Whitespace(t2) :: tl -> 
         let trivia = [eol(); tab(); region; eol(); eol(); t2] @ tl
         token.WithLeadingTrivia(trivia)
      | Whitespace(t1) :: tl -> token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString()); tab(); region] @ [eol(); eol()] @ formattedList)
      | _ -> token.WithLeadingTrivia(eol() :: tab() :: region :: formattedList)

   let closeRegion (token: SyntaxToken) (region: RegionType) = 
      if closedRegions.Contains region then token
      else
         closedRegions <- closedRegions.Add region
         Syntax.Trivia(Syntax.EndRegionDirectiveTrivia(true)) |> addRegion token

   let closeRegions (token: SyntaxToken) (activeRegions: RegionType list) = 
      let rec closeNext t l =
         match l with
         | hd :: tl -> closeNext (closeRegion t hd) tl
         | _        -> t
      closeNext token activeRegions

   let closeActiveRegions (token: SyntaxToken) = closeRegions token (Set.difference openedRegions closedRegions |> Set.toList)

   let openRegion (token: SyntaxToken) (region: RegionType) =
      if openedRegions.Contains region then token
      else
         let activeRegions = Set.difference openedRegions closedRegions |> Set.toList
         openedRegions <- openedRegions.Add region
         let updToken = SyntaxTree.ParseText("#region " + (getName region)).GetRoot().GetLeadingTrivia().First() |> addRegion token
         closeRegions updToken activeRegions

   override x.VisitToken token =
      let parent = token.Parent.ToString()
      if collector.OpenRegionMarkers.ContainsKey parent then
         match collector.OpenRegionMarkers.[parent] with
         | Ctors      -> openRegion token Ctors
         | Events     -> openRegion token Events
         | Fields     -> openRegion token Fields
         | Properties -> openRegion token Properties
         | Methods    -> openRegion token Methods
         | Other      -> base.VisitToken token
      else
         match token.Parent with
         | :? ClassDeclarationSyntax when token.Kind = SyntaxKind.CloseBraceToken -> closeActiveRegions token
         | _                                                                      -> base.VisitToken token


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
   