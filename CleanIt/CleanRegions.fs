module CleanRegions

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp
open Roslyn.Services.Formatting


let (|RegionDirective|_|) (expr:SyntaxTrivia) =                  if expr.Kind = SyntaxKind.RegionDirectiveTrivia then Some(expr) else None
let (|EndRegionDirective|_|) (expr:SyntaxTrivia) =               if expr.Kind = SyntaxKind.EndRegionDirectiveTrivia then Some(expr) else None
let (|EndOfLine|_|) (expr:SyntaxTrivia) =                        if expr.Kind = SyntaxKind.EndOfLineTrivia then Some(expr) else None
let (|Whitespace|_|) (expr:SyntaxTrivia) =                       if expr.Kind = SyntaxKind.WhitespaceTrivia then Some(expr) else None
let (|ConstructorDeclaration|_|) (expr:SyntaxNode) =             if expr :? ConstructorDeclarationSyntax then Some(expr :?> ConstructorDeclarationSyntax) else None
let (|EventFieldDeclaration|_|) (expr:SyntaxNode) =              if expr :? EventFieldDeclarationSyntax then Some(expr :?> EventFieldDeclarationSyntax) else None
let (|FieldDeclaration|_|) (expr:SyntaxNode) =                   if expr :? FieldDeclarationSyntax then Some(expr :?> FieldDeclarationSyntax) else None
let (|PropertyDeclaration|_|) (expr:SyntaxNode) =                if expr :? PropertyDeclarationSyntax then Some(expr :?> PropertyDeclarationSyntax) else None
let (|MethodDeclaration|_|) (expr:SyntaxNode) =                  if expr :? MethodDeclarationSyntax then Some(expr :?> MethodDeclarationSyntax) else None
let (|ClassDeclaration|_|) (expr:SyntaxNode) =                   if expr :? ClassDeclarationSyntax then Some(expr :?> ClassDeclarationSyntax) else None


let eol() = Syntax.EndOfLine("\r\n", false)
let tab() = Syntax.Whitespace("\t", false)


type Construct =
    | DependencyProperty of string * FieldDeclarationSyntax * PropertyDeclarationSyntax
    | AutoGenProperty    of string * FieldDeclarationSyntax * PropertyDeclarationSyntax
    
let getConstructName = function
   | DependencyProperty(name, _, _) -> name
   | AutoGenProperty(name, _, _)    -> name

let getConstructNodes = function
   | DependencyProperty(name, f, p) -> [f :> MemberDeclarationSyntax; p :> MemberDeclarationSyntax]
   | AutoGenProperty(name, f, p)    -> [p :> MemberDeclarationSyntax; f :> MemberDeclarationSyntax]


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


type MemberType =
   | Ctor     
   | Event    
   | Field    
   | Property 
   | Method   
   | Construct
   | Class
 
let toMemberType (node: SyntaxNode) =
   match node with
   | :? ConstructorDeclarationSyntax -> Ctor
   | :? EventFieldDeclarationSyntax  -> Event
   | :? FieldDeclarationSyntax       -> Field
   | :? PropertyDeclarationSyntax    -> Property
   | :? MethodDeclarationSyntax      -> Method
   | :? ClassDeclarationSyntax       -> Class
   | _                               -> raise (new System.NotSupportedException())

let toSignature (node: SyntaxNode) =
   let join (l:string array) = if l.Length = 0 then "" else " " + System.String.Join(":", l)
   let getParams (pSyntax: ParameterListSyntax) = (pSyntax.Parameters |> Seq.map (fun t -> t.Type.ToString())).ToArray() |> join
   let getModifiers (tokens: SyntaxTokenList) = (tokens |> Seq.map (fun t -> t.ValueText)).ToArray() |> join
   match node with
   | ConstructorDeclaration(n) -> ".ctor" + (getParams n.ParameterList) + (getModifiers n.Modifiers)
   | EventFieldDeclaration(n)  -> n.Declaration.Variables.First().Identifier.ValueText
   | FieldDeclaration(n)       -> n.Declaration.Variables.First().Identifier.ValueText
   | PropertyDeclaration(n)    -> n.Identifier.ValueText
   | MethodDeclaration(n)      -> n.Identifier.ValueText + (getParams n.ParameterList)
   | ClassDeclaration(n)       -> n.Identifier.ValueText
   | _                         -> raise (new System.NotSupportedException())


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


let rec getClassName (node: SyntaxNode) =
   if node = null then null
   else if node :? ClassDeclarationSyntax then (node :?> ClassDeclarationSyntax).Identifier.ValueText
   else getClassName node.Parent


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

   let mutable members = List.empty<MemberDeclarationSyntax>

   let membersMap = lazy (
      let toMemberMap (m: MemberDeclarationSyntax seq) = m |> Seq.map (fun t -> (toSignature t, t)) |> Seq.sortBy (fun (t, k) -> t) |> Map.ofSeq
      let toClassMap (m: MemberDeclarationSyntax seq) =  
         let members = m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, toMemberMap s)) |> Map.ofSeq
         if members.ContainsKey Field = false || members.ContainsKey Property = false then members
         else
            let getDependencyProperty name =
               let fieldName = name + "Property"
               if members.[Field].ContainsKey fieldName = false then None else
                  let fp = members.[Field].[fieldName] :?> FieldDeclarationSyntax
                  if fp.Declaration.Type.ToString() = "DependencyProperty" && (isStatic fp.Modifiers) then Some(fp :> MemberDeclarationSyntax) else None
            let getAutoGeneratedProperty name =
               let fieldName = "p_" + name
               if members.[Field].ContainsKey fieldName = false then None else
                  let fp = members.[Field].[fieldName] :?> FieldDeclarationSyntax
                  let pp = members.[Property].[name] :?> PropertyDeclarationSyntax
                  if fp.Declaration.Type.ToString() = pp.Type.ToString() then Some(fp :> MemberDeclarationSyntax) else None
            let dpCandidates = members.[Property] |> Map.toSeq |> Seq.map (fun (k, v) -> (v, getDependencyProperty k)) |> Seq.filter (fun (k, v) -> v.IsSome) |> Seq.collect (fun (k, v) -> [k; v.Value])
            let agCandidates = members.[Property] |> Map.toSeq |> Seq.map (fun (k, v) -> (v, getAutoGeneratedProperty k)) |> Seq.filter (fun (k, v) -> v.IsSome) |> Seq.collect (fun (k, v) -> [k; v.Value])
            m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, toMemberMap s)) |> Map.ofSeq
            members
      members |> Seq.groupBy (fun t -> getClassName t) |> Seq.map (fun (k, s) -> (k, toClassMap s)) |> Map.ofSeq
   )

   let mutable constructs = Map.empty<string, Construct>
   let mutable constructors = Map.empty<string, ConstructorDeclarationSyntax>
   let mutable events = Map.empty<string, EventFieldDeclarationSyntax>
   let mutable fields = Map.empty<string, FieldDeclarationSyntax>
   let mutable properties = Map.empty<string, PropertyDeclarationSyntax>
   let mutable methods = Map.empty<string, MethodDeclarationSyntax>

   let mutable openRegionMarkers = Map.empty<string, RegionType>

   let collectConstructs name =
      let dpPropName = name + "Property"
      let propBackingFieldName = "p_" + name
      if fields.ContainsKey(dpPropName) && properties.ContainsKey(name) then
         let fNode = fields.[dpPropName]
         let pNode = properties.[name]
         if (isStatic fNode.Modifiers) && fNode.Declaration.Type.ToString() = "DependencyProperty" then
            let c = DependencyProperty(name, fNode, pNode)
            constructs <- constructs.Add (name, c)
            fields <- fields.Remove(dpPropName)
            properties <- properties.Remove(name)
      else if fields.ContainsKey(propBackingFieldName) && properties.ContainsKey(name) then
         let fNode = fields.[propBackingFieldName]
         let pNode = properties.[name]
         if fNode.Declaration.Type.ToString() = pNode.Type.ToString() then
            let c = AutoGenProperty(name, fNode, pNode)
            constructs <- constructs.Add (name, c)
            fields <- fields.Remove(propBackingFieldName)
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

//   let collectMember (node: SyntaxNode) =
//      let mType = toMemberType node
//      let cName = getClassName node
//      if members.ContainsKey cName  = false then members <- members.Add (cName, Map.empty)
//      if members.[cName].ContainsKey mType = false then members.[cName] <- 
    
   member x.Members with get() = membersMap

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

   override x.VisitClassDeclaration node =
      let rec getParentClass (n: SyntaxNode) = if n = null then null else match n.Parent with | ClassDeclaration(c) -> c | _ -> getParentClass n.Parent 
      let parentClass = getParentClass node
      if parentClass = null then base.VisitClassDeclaration node 
      else 
         members <- (node :> MemberDeclarationSyntax) :: members
         null

   override x.VisitConstructorDeclaration node = 
      members <- (node :> MemberDeclarationSyntax) :: members
      //constructors <- constructors.Add (node.ParameterList.ChildNodes().Count().ToString() + getModifiers(node.Modifiers), node)
      null

   override x.VisitEventFieldDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      //events <- events.Add (node.Declaration.Variables.First().Identifier.ValueText, node)
      null

   override x.VisitFieldDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      //let name = node.Declaration.Variables.First().Identifier.ValueText
      //fields <- fields.Add (name, node)
      //collectConstructs (if name.EndsWith "Property" then name.Substring(0, name.Length - 8) else if name.StartsWith "p_" then name.Substring(2) else name)
      null

   override x.VisitPropertyDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      //properties <- properties.Add (node.Identifier.ValueText, node)
      //collectConstructs node.Identifier.ValueText
      null

   override x.VisitMethodDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      //methods <- methods.Add (node.Identifier.ValueText + getSignature(node.ParameterList), node)
      null


type MemberArranger(collector: MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let sgn = toSignature node
      if collector.Members.Value.ContainsKey sgn then
         let classMembers = collector.Members.Value.[sgn]
         let extend (mType: MemberType) (node: ClassDeclarationSyntax) = 
            if classMembers.ContainsKey mType then
               let members = classMembers.[mType] |> Map.toList |> List.map snd
               node.WithMembers(Syntax.List(members.Concat(node.Members)))
            else node
         node |> extend Class |> extend Method |> extend Property |> extend Field |> extend Event |> extend Ctor :> SyntaxNode
      else base.VisitClassDeclaration node

//      let extend (members:SyntaxList<MemberDeclarationSyntax> option) (node:ClassDeclarationSyntax) =
//         match members with
//         | Some(list) -> node.WithMembers(Syntax.List(list.Concat(node.Members)))
//         | None       -> node
//      base.VisitClassDeclaration (node |> extend collector.Methods |> extend collector.Properties |> extend collector.Fields |> extend collector.Events |> extend collector.Ctors)


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
      | Whitespace(t1) :: tl -> token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString()); region] @ [eol(); eol()] @ formattedList)
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
   