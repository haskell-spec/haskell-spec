import HaskellSpec.Source.Lang
import HaskellSpec.Source.ImportExport
import HaskellSpec.Names
import HaskellSpec.NonEmpty

namespace Source

/--
```text
conDecl ∈ ConstructorDecl → J t₁ … tₙ                 k ≥ 0
                          | J { v₁ ∷ t₁ … vₙ ∷ tₙ }   k ≥ 0
```
-/
inductive ConstructorDecl : Type where
  | poscon: Names.Constructor → List TypeExpression → ConstructorDecl
  | labcon: Names.Constructor → List (Names.QVariable × TypeExpression) → ConstructorDecl

/--
```text
conDecls ∈ ConstructorDecls → conDecl₁ | … | conDeclₙ   n ≥ 1
```
-/
@[reducible]
def ConstructorDecls : Type := NonEmpty ConstructorDecl

/--
```text
ctDecl ∈ Class or type → type S u₁ ... uₖ = t                              k ≥ 0
                       | data cx => S u₁ ... uₖ = conDecls                 k ≥ 0
                       | class cx => B u where sigs; bind₁; ...; bindₙ     k ≥ 0
```
-/
inductive ClassOrType : Type where
  | ct_type :
      Names.Type_Name
    → List Names.Type_Variable
    → TypeExpression
    → ClassOrType
  | ct_data :
      Context
    → Names.Type_Name
    → List Names.Type_Variable
    → ConstructorDecls
    → ClassOrType
  | ct_class :
      Context
    → Names.Class_Name
    → Names.Type_Variable
    → List Signature
    → List Binding
    → ClassOrType

/--
```text
instDecl ∈ InstanceDecl → instance cx => C t where bind₁; …; bindₙ    n ≥ 0
```
-/
structure InstanceDecl : Type where
  context : Context
  className : Names.Class_Name
  instance_head : TypeExpression
  binds : List Binding

/--
```text
instDecls ∈ InstanceDecls → instDecl₁; …; instDeclₙ   n ≥ 0
```
-/
def InstanceDecls : Type := List InstanceDecl

/--
```text
ctDecls ∈ Classes and types → [ctDecl₁;...;ctDeclₙ then ctDecls]
                              n ≥ 1
```
-/
inductive ClassesAndTypes : Type where
  | empty
  | decls : NonEmpty ClassOrType → ClassesAndTypes → ClassesAndTypes



/--
Reconstruct the type of the class assertion. e.g.
   classAssertionType (C u (t₁ … tₖ)) = u t₁ … tₖ
-/
def classAssertionType (ca : ClassAssertion) : TypeExpression :=
   List.foldl TypeExpression.app (TypeExpression.var ca.var) ca.args

/--
```text
body ∈ Module body → ctDecls; instDecls; binds
```
-/
structure ModuleBody : Type where
  ctDecls : ClassesAndTypes
  instDecls : InstanceDecls
  binds : Binds

/--
```text
mod ∈ Module → module M (ent₁,..., entₖ) where imp₁;...;impₙ;body
               k, n ≥ 0
```
-/
structure Module : Type where
  name : Names.Module_Name
  exports : List Entity
  imports : List Import
  body : ModuleBody

end Source
