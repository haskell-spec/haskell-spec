import HaskellSpec.Names
import HaskellSpec.NonEmpty
import HaskellSpec.SemanticTypes
/-!
Figure 6
-/

namespace Target
/--
From Fig. 3:
```
literal ∈ Literal → char
                  | string
                  | integer
                  | float
```
-/
inductive Literal : Type where
  | char : Char → Literal
  | string : String → Literal
  | integer : Int → Literal
  deriving Repr


/--
```text
t ∈ Type expression → u
                    | T
                    | t₁ t₂
```
-/
inductive TypeExpression : Type where
  | var      : Names.Type_Variable → TypeExpression
  | typename : Names.Type_Name → TypeExpression
  | app      : TypeExpression → TypeExpression → TypeExpression
  deriving Repr

/--
```text
class ∈ ClassAssertion → C (u t₁ … tₖ)   k ≥ 0
```
-/
structure ClassAssertion : Type where
  name : Names.Class_Name
  var : Names.Type_Variable
  args : List TypeExpression
  deriving Repr

/--
```text
cx ∈ Context → (class₁,...,classₖ)
                k ≥ 0
```
-/
def Context : Type := List ClassAssertion
  deriving Repr

mutual
  /--
  ```text
    p ∈ Pattern → v : σ
                | K p₁ … pₙ      k ≥ 0
                | K {fp₁ … fpₙ}  k ≥ 0
                | v : σ @ p
                | ~p
                | _
                | { e }
                | v : σ {e1, e2}
    fp ∈ FieldPattern → x = p
  ```
  -/
  inductive Pattern : Type where
    | var : Names.Variable → SemTy.TypeScheme →  Pattern
    | constructor : Names.QConstructor → List Pattern → Pattern
    | constructor_labelled : Names.QConstructor → List (Names.Variable × Pattern) → Pattern
    | as : Names.Variable → SemTy.TypeScheme → Pattern → Pattern
    | lazy : Pattern → Pattern
    | wildcard : Pattern
    | exp : Expression → Pattern
    | char : Char → Pattern -- Seems to be omitted in Faxen?
    | string : String → Pattern -- Seems to be omitted in Faxen?
    deriving Repr

  /--
  ```text
    binds ∈ Bindings → bind₁; ... ; bindₙ n > 0
                     | rec bind₁; ... ; bind n
  ```
  -/
  inductive Binds : Type where
    | recursive : List Binding → Binds
    | non_recursive : List Binding → Binds
    deriving Repr

  /--
  ```text
    bind ∈ Binding → x match₁ [] … [] matchₙ    n ≥ 1
                   | p gdes
  ```
  -/
  inductive Binding : Type where
    | bind_match : Names.QVariable → NonEmpty Match → Binding
    | bind_pat : Pattern → GuardedExprs → Binding
    deriving Repr

  /--
  ```text
    match ∈ Match → p₁ … pₖ gdes    k ≥ 1
  ```
  -/
  structure Match : Type where
    patterns : NonEmpty Pattern
    gdes : GuardedExprs
    deriving Repr

  /--
  ```text
    gdes ∈ GuardedExprs → gde₁ … gdeₙ where binds   n ≥ 1
  ```
  -/
  structure GuardedExprs : Type where
    gdes : NonEmpty GuardedExp
    binds : Binds
    deriving Repr


  /--
  ```text
    gde ∈ GuardedExpr → | e₁ = e₂
  ```
  -/
  structure GuardedExp : Type where
    guard : Expression
    body : Expression
    deriving Repr

  /--
  ```text
    e ∈ Expression → x
                   | literal
                   | K
                   | λ p₁ … pₖ → e                     k ≥ 1
                   | e₁ e₂
                   | let binds in e
                   | case e of match₁ [] … [] matchₙ   n ≥ 1
                   | [e | quals]
                   | e ⇐ {fbind₁, …, fbindₖ}           k ≥ 0
                   | e {fbind₁, …, fbindₖ}             k ≥ 0
                   | e τ₁ … τₖ                         k ≥ 1
                   | Λ α₁ … αₖ.e                       k ≥ 1
  ```
  -/
  inductive Expression : Type where
    | var : Names.QVariable → Expression
    | lit : Literal → Expression
    | constr : Names.QConstructor → Expression
    | abs : NonEmpty Pattern → Expression → Expression
    | app : Expression → Expression → Expression
    | let_bind : Binds → Expression → Expression
    | case : Expression → NonEmpty Match → Expression
    | listComp : Expression → Qualifiers → Expression
    | recUpd : Expression → List FieldBinding → Expression
    | recConstr : Expression → List FieldBinding → Expression
    | typ_app : Expression → NonEmpty SemTy.TypeS → Expression
    | typ_abs : NonEmpty Names.Type_Variable → Expression → Expression
    deriving Repr

  /--
  ```text
  stmts ∈ Statements → p <- e; stmts
                     | let binds; stmts
                     | e; stmts
                     | e
  ```
  -/
  inductive Statements : Type where
      /--
      ```text
      p <- e; stmts
      ```
      -/
    | mbind : Pattern → Expression → Statements → Statements
      /--
      ```text
      let binds; stmts
      ```
      -/
    | lbind : Binds → Statements → Statements
      /--
      ```text
      e; stmts
      ```
      -/
    | seq : Expression → Statements → Statements
    | last : Expression → Statements
    deriving Repr

  /--
  ```text
  quals ∈ Qualifiers → p <- e, quals
                     | let binds, quals
                     | e, quals
                     | ε
  ```
  -/
  inductive Qualifiers : Type where
    | list_bind : Pattern → Expression → Qualifiers → Qualifiers
    | lbind : Binds → Qualifiers → Qualifiers
    | guard : Expression → Qualifiers → Qualifiers
    | empty : Qualifiers
    deriving Repr

  /--
  ```text
  fbind ∈ FieldBinding → x = e
  ```
  -/
  inductive FieldBinding : Type where
    | fb_bind : Names.QVariable → Expression → FieldBinding
    deriving Repr
end

def apps (e : Expression)(es : List Expression) : Expression :=
  es.foldl Expression.app e

-- A helper to handle the case of an empty list in a typ_app
def typ_app_ (e : Expression) (ts : List SemTy.TypeS) : Expression :=
  (Option.elim (fromList ts) e (Target.Expression.typ_app e))

/--
```text
instDecl ∈ InstanceDecl → instance cx => C t where bind₁; …; bindₙ    n ≥ 0
instDecls ∈ InstanceDecls → instDecl₁; …; instDeclₙ   n ≥ 0
```
-/
structure InstanceDecl : Type where
  context : Context
  className : Names.Class_Name
  instance_head : TypeExpression
  binds : List Binding
  deriving Repr


/--
```text
conDecl ∈ ConstructorDecl → J t₁ … tₙ                 k ≥ 0
                          | J { v₁ ∷ t₁ … vₙ ∷ tₙ }   k ≥ 0
conDecls ∈ ConstructorDecls → conDecl₁ | … | conDeclₙ   n ≥ 1
```
-/
inductive ConstructorDecl : Type where
  | poscon: Names.Constructor → List TypeExpression → ConstructorDecl
  | labcon: Names.Constructor → List (Names.QVariable × TypeExpression) → ConstructorDecl
  deriving Repr

/--
```text
sig ∈ Signature → v :: cx => t
sigs ∈ Signatures → sig₁; …; sigₙ   n ≥ 0
```
-/
inductive Signature : Type where
  | sig : Names.QVariable → Context → TypeExpression → Signature
  deriving Repr

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
    → NonEmpty ConstructorDecl
    → ClassOrType
  | ct_class :
      Context
    → Names.Class_Name
    → Names.Type_Variable
    → List Signature
    → List Binding
    → ClassOrType
  deriving Repr

/--
```text
ctDecls ∈ Classes and types → [ctDecl₁;...;ctDeclₙ then ctDecls]
                              n ≥ 1
```
-/
inductive ClassesAndTypes : Type where
  | empty
  | decls : NonEmpty ClassOrType → ClassesAndTypes → ClassesAndTypes
  deriving Repr

/--
```text
body ∈ Module body → ctDecls; instDecls; binds
```
-/
structure ModuleBody : Type where
  ctDecls : ClassesAndTypes
  instDecls : List InstanceDecl
  binds : Binds
  deriving Repr

/--
```text
typeDecl ∈ TypeDeclaration → data χ α₁ … αₖ = conDecl₁ | … | conDeclsₙ    k ≥ 0
                                                                          n ≥ 1
```
-/
inductive TypeDeclaration : Type where
  | typeDecl :
      -- Chi ->
      -- List Alphas ->
      NonEmpty ConstructorDecl ->
      TypeDeclaration
  deriving Repr

/--
```text
typeDecls ∈ TypeDeclarations → typeDecl₁; …; typeDeclₙ    n ≥ 0
mod ∈ Module → module M where typeDecls; binds
```
-/
structure Module : Type where
  name : Names.Module_Name -- Use QModule:Name in the future?
  decls : List TypeDeclaration
  deriving Repr

end Target
