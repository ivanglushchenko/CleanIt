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


type MemberType =
   | Ctor     
   | Event    
   | Field    
   | Property 
   | Method   
   | Construct
   | Class

   override x.ToString() = 
      match x with
      | Ctor      -> "Member: Ctor"
      | Event     -> "Member: Event"
      | Field     -> "Member: Field"
      | Property  -> "Member: Property"
      | Method    -> "Member: Method"
      | Construct -> "Member: Construct"
      | Class     -> "Member: Class"
 

let toRegionName = function
   | Ctor      -> ".ctors"
   | Event     -> "Events"
   | Field     -> "Fields"
   | Property  -> "Properties"
   | Method    -> "Methods"
   | Construct -> raise (new System.NotSupportedException())
   | Class     -> "Internal Classes"

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

let rec getParentClass (node: SyntaxNode) = 
   if node = null then null 
   else match node.Parent with | ClassDeclaration(c) -> c | _ -> getParentClass node.Parent 

type MemberCollector() = 
   inherit SyntaxRewriter(false)

   let isStatic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "static")
   let isPublic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "public")

   let mutable members = List.empty<MemberDeclarationSyntax>
   let mutable classes = Map.empty<string, string>

   let membersMap = lazy (
      let toClassName (m: MemberDeclarationSyntax) =
         let className = getClassName m
         if m :? ClassDeclarationSyntax then 
            if classes.ContainsKey className then classes.[className]
            else className
         else className
      let toClassMap (m: MemberDeclarationSyntax seq) =  
         let members = m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, s |> Seq.map (fun t -> (toSignature t, t)) |> Map.ofSeq)) |> Map.ofSeq
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
         let getConstructs (getter: string -> MemberDeclarationSyntax option) (reverseOutput: bool) =
            if members.ContainsKey Field = false || members.ContainsKey Property = false then Seq.empty
            else members.[Property] |> Map.toSeq |> Seq.sortBy (fun (k, v) -> k) |>  Seq.map (fun (k, v) -> (v, getter k)) |> Seq.filter (fun (k, v) -> v.IsSome) |> Seq.collect (fun (k, v) -> if reverseOutput then [k; v.Value] else [v.Value; k])
         let constructMembers = Seq.append (getConstructs getDependencyProperty false) (getConstructs getAutoGeneratedProperty true)
         let toMemberMapWithConstructs (mt: MemberType) (m: MemberDeclarationSyntax seq) =
            let filteredMembers = m |> Seq.filter (fun t -> constructMembers |> Seq.exists (fun v -> v = t) = false) |> Seq.map (fun t -> (toSignature t, t)) |> Seq.sortBy fst |> Seq.map snd
            if mt = Property then Seq.append constructMembers filteredMembers else filteredMembers
         m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, toMemberMapWithConstructs k s)) |> Map.ofSeq
      members |> Seq.groupBy (fun t -> toClassName t) |> Seq.map (fun (k, s) -> (k, toClassMap s)) |> Map.ofSeq
   )

   let openRegionMarkers = lazy (
      membersMap.Value |> Map.map (fun className v -> v |> Map.map (fun memberType members -> members.First().ToString()) |> Map.toSeq |> Seq.map (fun (k, v) -> (v, k)) |> Map.ofSeq)
   )

   member x.Members with get() = membersMap
   member x.OpenRegionMarkers with get() = openRegionMarkers

   override x.VisitClassDeclaration node =
      let parentClass = getParentClass node
      if parentClass = null then base.VisitClassDeclaration node
      else
         let className = getClassName node
         let parentClassName = getClassName parentClass
         classes <- classes.Add (className, parentClassName)
         let updNode = base.VisitClassDeclaration node
         members <- (updNode :?> MemberDeclarationSyntax) :: members
         null

   override x.VisitConstructorDeclaration node = 
      members <- (node :> MemberDeclarationSyntax) :: members
      null

   override x.VisitEventFieldDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      null

   override x.VisitFieldDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      null

   override x.VisitPropertyDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      null

   override x.VisitMethodDeclaration node =
      members <- (node :> MemberDeclarationSyntax) :: members
      null


type MemberArranger(collector: MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let rec extendClass (node: ClassDeclarationSyntax) =
         let className = toSignature node
         let classMembers = collector.Members.Value.[className]
         let extend (memberType: MemberType) (node: ClassDeclarationSyntax) = 
            if classMembers.ContainsKey memberType then
               let members = node.Members |> Seq.toList |> List.append (classMembers.[memberType] |> Seq.toList |> extendClasses)
               node.WithMembers(Syntax.List(members))
            else node
         node |> extend Class |> extend Method |> extend Property |> extend Field |> extend Event |> extend Ctor
      and extendClasses (l: MemberDeclarationSyntax list) =
         match l with
         | ClassDeclaration(c) :: tl -> extendClass(c) :> MemberDeclarationSyntax :: extendClasses(tl)
         | hd :: tl                  -> hd :: extendClasses(tl)
         | _                         -> []
      extendClass node :> SyntaxNode


type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   let mutable openedRegions = Set.empty<MemberType>
   let mutable closedRegions = Set.empty<MemberType>

   let addRegion (token: SyntaxToken) (region: SyntaxTrivia) =
      let formattedList = (token.LeadingTrivia |> Seq.toList)
      match formattedList with
      | EndOfLine(t1) :: Whitespace(t2) :: tl -> 
         let trivia = [eol(); tab(); region; eol(); eol(); t2] @ tl
         token.WithLeadingTrivia(trivia)
      | Whitespace(t1) :: tl -> token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString()); region] @ [eol(); eol()] @ formattedList)
      | _ -> token.WithLeadingTrivia(eol() :: tab() :: region :: formattedList)

   let closeRegion (token: SyntaxToken) (region: MemberType) = 
      if closedRegions.Contains region then token
      else
         closedRegions <- closedRegions.Add region
         Syntax.Trivia(Syntax.EndRegionDirectiveTrivia(true)) |> addRegion token

   let closeRegions (token: SyntaxToken) (activeRegions: MemberType list) = 
      let rec closeNext t l =
         match l with
         | hd :: tl -> closeNext (closeRegion t hd) tl
         | _        -> t
      closeNext token activeRegions

   let closeActiveRegions (token: SyntaxToken) = closeRegions token (Set.difference openedRegions closedRegions |> Set.toList)

   let openRegion (token: SyntaxToken) (region: MemberType) =
      if openedRegions.Contains region then token
      else
         let activeRegions = Set.difference openedRegions closedRegions |> Set.toList
         openedRegions <- openedRegions.Add region
         let updToken = SyntaxTree.ParseText("#region " + (toRegionName region)).GetRoot().GetLeadingTrivia().First() |> addRegion token
         closeRegions updToken activeRegions

   override x.VisitClassDeclaration node =
      let parentClass = getParentClass node
      if parentClass = null then base.VisitClassDeclaration node
      else node :> SyntaxNode

   override x.VisitToken token =
      let className = getClassName token.Parent
      let parent = token.Parent.ToString()
      if collector.OpenRegionMarkers.Value.ContainsKey className && collector.OpenRegionMarkers.Value.[className].ContainsKey parent then
         openRegion token collector.OpenRegionMarkers.Value.[className].[parent]
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
      | _                          -> token


let cleanRegions (root:CompilationUnitSyntax) =
   let collector = MemberCollector()
   let cleanRoot = root.Accept(RegionRemover()).Accept(collector)
   let fmtOptions = FormattingOptions(false, 4, 4)
   let fmtHelper = FormatHelper()
   cleanRoot.Accept(MemberArranger(collector)).Accept(RegionRewriter(collector))//.Format(fmtOptions).GetFormattedRoot() :?> SyntaxNode |> fmtHelper.Visit

//var formattedCode = new CodeBeautifier().Visit(root.Format()).GetFullText();
   