module CleanRegions

open System.Linq
open Roslyn.Compilers
open Roslyn.Compilers.CSharp
open Roslyn.Compilers.Common
open Roslyn.Services
open Roslyn.Services.CSharp
open Roslyn.Services.Formatting

/// ----------------------------------------------------------
/// Some active patterns to help with parsing syntax trees
/// ----------------------------------------------------------
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


/// ----------------------------------------------------------
/// Represents one of the supported members types.
/// ----------------------------------------------------------
type MemberType =
   | Ctor     
   | Event    
   | Field    
   | Property 
   | Method   
   | Class

   override x.ToString() = 
      match x with
      | Ctor      -> "Member: Ctor"
      | Event     -> "Member: Event"
      | Field     -> "Member: Field"
      | Property  -> "Member: Property"
      | Method    -> "Member: Method"
      | Class     -> "Member: Class"
 

let toRegionName = function
   | Ctor      -> ".ctors"
   | Event     -> "Events"
   | Field     -> "Fields"
   | Property  -> "Properties"
   | Method    -> "Methods"
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

// Signature is a string which uniquely represents a syntax tree member
let toSignature (node: SyntaxNode) =
   let join (l:string array) = if l.Length = 0 then "" else " " + System.String.Join(":", l)
   let getParams (pSyntax: ParameterListSyntax) = (pSyntax.Parameters |> Seq.map (fun t -> t.Type.ToString())).ToArray() |> join
   let getModifiers (tokens: SyntaxTokenList) = (tokens |> Seq.map (fun t -> t.ValueText)).ToArray() |> join
   match node with
   | ConstructorDeclaration(n) -> ".ctor" + (getParams n.ParameterList) + (getModifiers n.Modifiers)
   | EventFieldDeclaration(n)  -> "event:" + n.Declaration.Variables.First().Identifier.ValueText   
   | FieldDeclaration(n)       -> "field:" + n.Declaration.Variables.First().Identifier.ValueText   
   | PropertyDeclaration(n)    -> "prop:" + n.Identifier.ValueText                                  
   | MethodDeclaration(n)      -> "method:" + n.Identifier.ValueText + (getParams n.ParameterList)  
   | ClassDeclaration(n)       -> "class:" + n.Identifier.ValueText                                 
   | _                         -> null


/// ----------------------------------------------------------
/// Visitor which removes regions from a syntax tree
/// ----------------------------------------------------------
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


let rec getClassSignature (node: SyntaxNode) =
   if node = null then null
   else if node :? ClassDeclarationSyntax then toSignature node
   else getClassSignature node.Parent

let rec getParentClass (node: SyntaxNode) = 
   if node = null then null 
   else match node.Parent with | ClassDeclaration(c) -> c | _ -> getParentClass node.Parent 


/// ----------------------------------------------------------
/// Visitor which collects (and removes) supported members from a syntax tree
/// ----------------------------------------------------------
type MemberCollector() = 
   inherit SyntaxRewriter(false)

   let isStatic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "static")
   let isPublic (tokens: SyntaxTokenList) = tokens |> Seq.exists (fun t -> t.ValueText = "public")

   // Extracts parts of dependency property declarations
   let (|DependencyPropertyConstruct|_|) (members: Map<MemberType, Map<string, MemberDeclarationSyntax>>) (propertySignature: string) = 
      let name = if propertySignature.StartsWith("prop:") then "field:" + propertySignature.Substring(5) else "field:" + propertySignature
      let fieldName = name + "Property"
      if members.[Field].ContainsKey fieldName = false then None else
         let fp = members.[Field].[fieldName] :?> FieldDeclarationSyntax
         if fp.Declaration.Type.ToString() = "DependencyProperty" && (isStatic fp.Modifiers) then Some([fp :> MemberDeclarationSyntax; members.[Property].[propertySignature]]) else None

   // Extracts parts of auto-generated property declarations
   let (|AutoGeneratedPropertyConstruct|_|) (members: Map<MemberType, Map<string, MemberDeclarationSyntax>>) (propertySignature: string) = 
      let name = if propertySignature.StartsWith("prop:") then propertySignature.Substring(5) else propertySignature
      let tryName fieldName = 
         if members.[Field].ContainsKey fieldName = false then None else
            let fp = members.[Field].[fieldName] :?> FieldDeclarationSyntax
            let pp = members.[Property].[propertySignature] :?> PropertyDeclarationSyntax
            if fp.Declaration.Type.ToString() = pp.Type.ToString() then Some([fp :> MemberDeclarationSyntax; members.[Property].[propertySignature]]) else None
      match tryName ("field:p_" + name) with
      | Some(x) -> Some(x)
      | None    -> tryName ("field:_" + name)

   let mutable members = List.empty<MemberDeclarationSyntax>
   let mutable classes = Map.empty<string, string>

   let membersMap = lazy (
      let toClassName (m: MemberDeclarationSyntax) =
         let className = getClassSignature m
         if m :? ClassDeclarationSyntax then if classes.ContainsKey className then classes.[className] else className
         else className
      let toClassMap (m: MemberDeclarationSyntax seq) =  
         let members = m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, s |> Seq.map (fun t -> (toSignature t, t)) |> Map.ofSeq)) |> Map.ofSeq
         let constructMembers = 
            if members.ContainsKey Field = false || members.ContainsKey Property = false then Seq.empty<MemberDeclarationSyntax>
            else members.[Property] |> Map.toSeq |> Seq.map fst |> Seq.sort |> Seq.collect (fun propertyName -> 
               match propertyName with
               | DependencyPropertyConstruct members [f; p] ->  seq [f; p]
               | AutoGeneratedPropertyConstruct members [f; p] -> seq [p; f]
               | _ -> Seq.empty)
         let toMemberMapWithConstructs (mt: MemberType) (m: MemberDeclarationSyntax seq) =
            let filteredMembers = m |> Seq.filter (fun t -> constructMembers |> Seq.exists (fun v -> v = t) = false) |> Seq.map (fun t -> (toSignature t, t)) |> Seq.sortBy fst |> Seq.map snd
            if mt = Property then Seq.append constructMembers filteredMembers else filteredMembers
         m |> Seq.groupBy (fun t -> toMemberType t) |> Seq.map (fun (k, s) -> (k, toMemberMapWithConstructs k s)) |> Map.ofSeq
      members |> Seq.groupBy (fun t -> toClassName t) |> Seq.map (fun (k, s) -> (k, toClassMap s)) |> Map.ofSeq
   )

   let openRegionMarkers = lazy (
      membersMap.Value |> Map.map (fun className v -> v |> Map.map (fun memberType members -> members.FirstOrDefault() |> toSignature) |> Map.toSeq |> Seq.map (fun (k, v) -> (v, k)) |> Map.ofSeq)
   )

   member x.Members with get() = membersMap
   member x.OpenRegionMarkers with get() = openRegionMarkers

   override x.VisitClassDeclaration node =
      let parentClass = getParentClass node
      if parentClass = null then base.VisitClassDeclaration node
      else
         let className = toSignature node
         let parentClassName = toSignature parentClass
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


/// ----------------------------------------------------------
/// Visitor which adds previously collected members to a syntax tree in the correct order
/// ----------------------------------------------------------
type MemberArranger(collector: MemberCollector) = 
   inherit SyntaxRewriter(false)

   override x.VisitClassDeclaration node =
      let rec extendClass (node: ClassDeclarationSyntax) =
         let className = toSignature node
         if collector.Members.Value.ContainsKey className then
             let classMembers = collector.Members.Value.[className]
             let extend (memberType: MemberType) (node: ClassDeclarationSyntax) = 
                if classMembers.ContainsKey memberType then
                   let members = node.Members |> Seq.toList |> List.append (classMembers.[memberType] |> Seq.toList |> extendClasses)
                   node.WithMembers(Syntax.List(members))
                else node
             node |> extend Class |> extend Method |> extend Property |> extend Field |> extend Event |> extend Ctor
         else node
      and extendClasses (l: MemberDeclarationSyntax list) =
         match l with
         | ClassDeclaration(c) :: tl -> extendClass(c) :> MemberDeclarationSyntax :: extendClasses(tl)
         | hd :: tl                  -> hd :: extendClasses(tl)
         | _                         -> []
      extendClass node :> SyntaxNode


/// ----------------------------------------------------------
/// Visitor which puts regions around groups of similiar members 
/// based on information provided during collecting phase
/// ----------------------------------------------------------
type RegionRewriter(collector:MemberCollector) = 
   inherit SyntaxRewriter(false)

   let mutable openedRegions = Map.empty<string, Set<MemberType>>
   let mutable closedRegions = Map.empty<string, Set<MemberType>>

   let addRegion (token: SyntaxToken) (region: SyntaxTrivia) =
      let formattedList = (token.LeadingTrivia |> Seq.toList)
      match formattedList with
      | EndOfLine(t1) :: Whitespace(t2) :: tl -> 
         token.WithLeadingTrivia([t2; region; eol(); eol(); t2] @ tl)
      | Whitespace(t1) :: tl -> 
         if token.Kind = SyntaxKind.CloseBraceToken then
            token.WithLeadingTrivia([eol(); Syntax.Whitespace(t1.ToFullString()); tab(); region] @ [eol()] @ formattedList)
         else if region.Kind = SyntaxKind.EndRegionDirectiveTrivia then
            token.WithLeadingTrivia([eol(); Syntax.Whitespace(t1.ToFullString()); region] @ [eol(); eol()] @ formattedList)
         else
            token.WithLeadingTrivia([Syntax.Whitespace(t1.ToFullString()); region] @ [eol(); eol()] @ formattedList)
      | _ -> token.WithLeadingTrivia(eol() :: tab() :: region :: formattedList)

   let closeRegion (token: SyntaxToken) (className: string) (region: MemberType) = 
      if closedRegions.[className].Contains region then token
      else
         closedRegions <- closedRegions |> Map.map (fun k v -> if k = className then v.Add region else v)
         Syntax.Trivia(Syntax.EndRegionDirectiveTrivia(true)) |> addRegion token

   let closeRegions (token: SyntaxToken) (className: string) (activeRegions: MemberType list) = 
      let rec closeNext t l =
         match l with
         | hd :: tl -> closeNext (closeRegion t className hd) tl
         | _        -> t
      closeNext token activeRegions

   let getActiveClassRegions (className: string) = if openedRegions.ContainsKey className then Set.difference openedRegions.[className] closedRegions.[className] |> Set.toList else List.empty

   let closeClassRegions (token: SyntaxToken) (className: string) = closeRegions token className (className |> getActiveClassRegions)

   let openRegion (token: SyntaxToken) (region: MemberType) =
      let parentClassName = token.Parent |> getParentClass |> toSignature
      if openedRegions.ContainsKey parentClassName && openedRegions.[parentClassName].Contains region then token
      else
         if openedRegions.ContainsKey parentClassName = false then
            openedRegions <- openedRegions.Add (parentClassName, Set.empty<MemberType>)
            closedRegions <- closedRegions.Add (parentClassName, Set.empty<MemberType>)
         let activeRegions = parentClassName |> getActiveClassRegions
         openedRegions <- openedRegions |> Map.map (fun k v -> if k = parentClassName then v.Add region else v)
         let updToken = SyntaxTree.ParseText("#region " + (toRegionName region)).GetRoot().GetLeadingTrivia().First() |> addRegion token
         closeRegions updToken parentClassName activeRegions

   override x.VisitClassDeclaration node =
      base.VisitClassDeclaration node

   override x.VisitToken token =
      match token.Parent with
      | ClassDeclaration(c) when token.Kind = SyntaxKind.CloseBraceToken -> closeClassRegions token (toSignature c)
      | _  ->
         let parentClass = getParentClass token.Parent
         if parentClass = null then token
         else
            let parentClassName = getClassSignature parentClass
            let rec getOuterSignature (node: SyntaxNode) =
               if node = null then null
               else 
                  let s = toSignature node
                  if s = null then getOuterSignature node.Parent else s
            let tokenOuterSignature = getOuterSignature token.Parent
            if collector.OpenRegionMarkers.Value.ContainsKey parentClassName && collector.OpenRegionMarkers.Value.[parentClassName].ContainsKey tokenOuterSignature then
               openRegion token collector.OpenRegionMarkers.Value.[parentClassName].[tokenOuterSignature]
            else token


/// ----------------------------------------------------------
/// Visitor which slightly formats final output
/// ----------------------------------------------------------
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
   cleanRoot.Accept(MemberArranger(collector)).Accept(RegionRewriter(collector)) :?> CompilationUnitSyntax
   //.Format(fmtOptions).GetFormattedRoot() :?> SyntaxNode |> fmtHelper.Visit