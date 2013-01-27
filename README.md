CleanIt walks through your solutions/projects and cleanes up C# code. Currently supported tasks include:

1. Sort and clean up usings

2. Puts #regions around constuructors/events/fields/properties/methods/internal classes

##How to use it
Clean up one file:

    cleanFile "path\to\MyFile.cs"

Clean up a project

    forEachFileInProject (Name("path\to\MyProject.csproj")) cleanNode

Clean up a solution:

    forEachFileInSolution (Name("path\to\MyProject.csproj")) cleanNode
