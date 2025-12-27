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
  ftv : α → List Names.Type_Variable

/--
```text
t ∈ Type expression → u
                    | T
                    | t₁ t₂
```
--/
inductive TypeExpression : Type where
  | var      : Names.Type_Variable → TypeExpression
  | typename : Names.QType_Name → TypeExpression
  | app      : TypeExpression → TypeExpression → TypeExpression

def ftv_type_expression (t : TypeExpression) : List Names.Type_Variable :=
  match t with
    | TypeExpression.var v => [v]
    | TypeExpression.typename _ => []
    | TypeExpression.app t₁ t₂ => (ftv_type_expression t₁) ++ (ftv_type_expression t₂)

instance ftv_type_expr : FTV TypeExpression where
  ftv :=  ftv_type_expression


/--

```text
class ∈ ClassAssertion → C (u t₁ … tₖ)   k ≥ 0
```
-/
structure ClassAssertion : Type where
  name : Names.QClassName
  var : Names.Type_Variable
  args : List TypeExpression

instance ftv_class_assertion : FTV ClassAssertion where
  ftv := λ ca => [ca.var] ++ (List.flatten (List.map (λ x => FTV.ftv x) ca.args))

/--
```text
cx ∈ Context → (class₁,...,classₖ)
                k ≥ 0
```
-/
abbrev Context : Type := List ClassAssertion

instance ftv_context : FTV Context where
  ftv := λ ctx => List.flatten (List.map (λ x => FTV.ftv x) ctx)

/--
```text
sig  ∈ Signature  → v :: cx => t
sigs ∈ Signatures → sig₁; …; sigₙ   n ≥ 0
```
-/
structure Signature : Type where
  var : Names.QVariable
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
    | bind_match : Names.QVariable → NonEmpty Match → Binding
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
    | var : Names.QVariable → Expression
    | lit : Literal → Expression
    | constr : Names.QConstructor → Expression
    | abs : NonEmpty Pattern → Expression → Expression
    | app : Expression → Expression → Expression
    | let_bind : Binds → Expression → Expression
    | case : Expression → NonEmpty Match → Expression
    | do_block : Statements → Expression
    | listComp : Expression → Qualifiers → Expression
    | listRange : Expression → Option Expression → Option Expression → Expression
    | recUpd : Expression → List (Names.QVariable × Expression) → Expression
    | recConstr : Names.QConstructor → List (Names.QVariable × Expression) → Expression

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
