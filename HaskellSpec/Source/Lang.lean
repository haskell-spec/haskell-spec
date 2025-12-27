import HaskellSpec.Names
import HaskellSpec.NonEmpty
import HaskellSpec.Source.Patterns
import HaskellSpec.Source.Literals

/-!
Figure 1 and 2
-/

namespace Source

/--
Compute free type variables
-/
class FTV (α : Type) where
  ftv : α → List Type_Variable

/--
```text
t ∈ Type expression → u
                    | T
                    | t₁ t₂
```
--/
inductive TypeExpression : Type where
  | var      : Type_Variable → TypeExpression
  | typename : QType_Name → TypeExpression
  | app      : TypeExpression → TypeExpression → TypeExpression

instance ftv_type_expression : FTV TypeExpression where
  ftv := λ _ => []

/--

```text
class ∈ ClassAssertion → C (u t₁ … tₖ)   k ≥ 0
```
-/
structure ClassAssertion : Type where
  name : QClassName
  var : Type_Variable
  args : List TypeExpression

instance ftv_class_assertion : FTV ClassAssertion where
  ftv := λ _ => []

/--
```text
cx ∈ Context → (class₁,...,classₖ)
                k ≥ 0
```
-/
abbrev Context : Type := List ClassAssertion

instance ftv_context : FTV Context where
  ftv := λ _ => []

/--
```text
sig  ∈ Signature  → v :: cx => t
sigs ∈ Signatures → sig₁; …; sigₙ   n ≥ 0
```
-/
structure Signature : Type where
  var : QVariable
  context : Context
  type : TypeExpression


mutual
  /--
  ```text
    binds ∈ Binds → [ sigs; bindG then binds]
    bindG ∈ BindGroup → bind₁; …; bindₙ   n ≥ 1
  ```
  --/
  inductive Binds : Type where
    | cons : List Signature → List Binds → Binds → Binds
    | empty : Binds


  /--
  ```text
    bind ∈ Binding → x match₁ [] … [] matchₙ    n ≥ 1
                   | p gdes
  ```
  --/
  inductive Binding : Type where
    | bind_match : QVariable → NonEmpty Match → Binding
    | bind_pat : Pattern → GuardedExprs → Binding

  /--
  ```text
    match ∈ Match → p₁ … pₖ gdes    k ≥ 1
  ```
  --/
  structure Match : Type where
    patterns : NonEmpty Pattern
    gdes : GuardedExprs

  /--
  ```text
    gdes ∈ GuardedExprs → gde₁ … gdeₙ where binds   n ≥ 1
  ```
  --/
  structure GuardedExprs : Type where
    gdes : NonEmpty GuardedExp
    binds : Binds

  /--
  ```text
    gde ∈ GuardedExpr → | e₁ = e₂
  ```
  --/
  structure GuardedExp : Type where
    guard : Expression
    body : Expression

  /--
  ```text
    e ∈ Expression       → x
                         | literal
                         | K
                         | \p₁ … pₖ → e                     k ≥ 1
                         | e₁ e₂
                         | let binds in e
                         | case e of match₁ [] … [] matchₙ   n ≥ 1
                         | do stmts
                         | [e | quals]
                         | [e₁ [,e₂] .. [e₃]]
                         | e ⇐ {fbind₁, …, fbindₖ}           k ≥ 0
                         | K {fbind₁, …, fbindₖ}             k ≥ 0
    fbind ∈ FieldBinding → x = e
  ```
  --/
  inductive Expression : Type where
    | var : QVariable → Expression
    | lit : Literal → Expression
    | constr : QConstructor → Expression
    | abs : NonEmpty Pattern → Expression → Expression
    | app : Expression → Expression → Expression
    | let_bind : Binds → Expression → Expression
    | case : Expression → NonEmpty Match → Expression
    | do_block : Statements → Expression
    | listComp : Expression → Qualifiers → Expression
    | listRange : Expression → Option Expression → Option Expression → Expression
    | recUpd : Expression → List (QVariable × Expression) → Expression
    | recConstr : QConstructor → List (QVariable × Expression) → Expression

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
end

end Source
