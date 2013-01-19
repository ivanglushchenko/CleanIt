module CodeRefactoring

//var workspace = Workspace.LoadStandAloneProject(args[0]);
//    var solution = workspace.CurrentSolution;
//    var newSolution = solution;
//    foreach (var project in solution.Projects)
//    {
//      foreach (var document in project.Documents)
//      {
//        if (document.LanguageServices.Language == LanguageNames.CSharp)
//        {
//          var tree = document.GetSyntaxTree().Root as SyntaxNode;
//          var newTree = tree.Deregionize();
//          if (tree != newTree)
//          {
//            var newText = newTree.GetFullTextAsIText();
//            newSolution = newSolution.UpdateDocument(document.Id, newText);
//          }
//        }
//      }
//    }
//    if (newSolution != solution)
//    {
//      workspace.ApplyChanges(solution, newSolution);
//    }

//[ExportCodeRefactoringProvider("RemoveComments", LanguageNames.CSharp)]
//class RemoveCommentsCodeRefactoringProvider : ICodeRefactoringProvider
//{
//    ICodeActionEditFactory editFactory;
//
//    [ImportingConstructor]
//    public RemoveCommentsCodeRefactoringProvider(ICodeActionEditFactory editFactory)
//    {
//        this.editFactory = editFactory;
//    }
//
//    public CodeRefactoring GetRefactoring(IDocument document, TextSpan textSpan, CancellationToken cancellationToken)
//    {
//        return new CodeRefactoring(new ICodeAction[] { new RemoveCommentsCodeAction(editFactory, document) });
//    }
//}
//
//class RemoveCommentsCodeAction : ICodeAction
//{
//    ICodeActionEditFactory editFactory;
//    IDocument document;
//
//    public RemoveCommentsCodeAction(ICodeActionEditFactory editFactory, IDocument document)
//    {
//        this.editFactory = editFactory;
//        this.document = document;
//    }
//
//    public string Description
//    {
//        get { return "Remove all comments"; }
//    }
//
//    public ICodeActionEdit GetEdit(CancellationToken cancellationToken)
//    {
//        var tree = (SyntaxTree)document.GetSyntaxTree(cancellationToken);
//
//        var commentTrivia = from t in tree.Root.DescendentTrivia()
//                            where t.Kind == SyntaxKind.SingleLineCommentTrivia ||
//                                  t.Kind == SyntaxKind.MultiLineCommentTrivia
//                            select t;
//
//        var newRoot = tree.Root.ReplaceTrivia(commentTrivia, (t1, t2) => SyntaxTriviaList.Empty);
//
//        return editFactory.CreateTreeTransformEdit(document.Project.Solution, tree, newRoot);
//    }
//
//    public ImageSource Icon
//    {
//        get { return null; }
//    }
//}