import HaskellSpec.Source.Lang
import HaskellSpec.Source.Module
import HaskellSpec.Target.Lang
import HaskellSpec.Environments
import HaskellSpec.SemanticTypes
import HaskellSpec.Forall2
import HaskellSpec.Elaboration.Kinding
open Kinding

/-
# Notations
-/

set_option quotPrecheck false in
set_option hygiene false in
notation  "《type》" te "," h "⊢" t "፥"  τ "▪" => type te h t τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《types》" te "," h "⊢" ts "፥"  τs "▪" => types te h ts τs

set_option quotPrecheck false in
set_option hygiene false in
notation  "《class》" ce "," te "," h "⊢" cls "፥" Γ "," τ "▪" => classR ce te h cls Γ τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《context》" ce "," te "," h "⊢" cx "፥" θ "▪" => context ce te h cx θ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《sig》" ge "⊢" sign "፥" ve "▪" => sig ge sign ve

set_option quotPrecheck false in
set_option hygiene false in
notation  "《sigs》" ge "⊢" sign "፥" ve "▪" => sigs ge sign ve

/-
# Utilities
-/

/-- A typename `T` applied to a list of arguments:
```text
type_apply T [t₁,t₂,t₃] = T t₁ t₂ t₃
```
TODO: Reverse order!
-/
def type_apply (T : QType_Name)
               (ts : List Source.TypeExpression)
               : Source.TypeExpression :=
  match ts with
  | [] => Source.TypeExpression.typename T
  | (t :: ts) => Source.TypeExpression.app (type_apply T ts) t

/-
# Judgements
-/

mutual
  /--
  Cp. Fig 18
  ```text
  TE, h ⊢ t : τ
  ```
  -/
  inductive type : Env.TE → Int
                 → Source.TypeExpression
                 → SemTy.TypeS
                 → Prop where
    | TVAR :
      ⟨u, α⟩ ∈ te₂ →
      ---------------------------------------------------------------------------
      《type》⟨te₁,te₂⟩, h ⊢ Source.TypeExpression.var u ፥ SemTy.TypeS.Variable α ▪

    | TCON :
      ⟨T, Env.TE_Item.DataType χ⟩ ∈ te₁ →
      --------------------------------------------------------------------------------------
      《type》⟨te₁,te₂⟩,h ⊢ Source.TypeExpression.typename T ፥ SemTy.TypeS.TypeConstructor χ ▪

      /--
      There are two complications when checking type synonyms:
      - Type synonyms always have to be fully applied.
      - In order to rule out cycles of recursive type synonyms such as
        ```
        type T = T
        ```
        we use a natural number index `h` in the judgement which must be greater than the number assigned
        to the type synonym in the context.
      -/
    | TSYN :
      ⟨T, Env.TE_Item.TypeSynonym χ g αs τ⟩ ∈ te₁ →
      g < h →
      《types》te, h ⊢ ts ፥ τs ▪ →
      Env.rng subst = τs →
      Env.dom subst = αs →
      ---------------------------------------------------------------------------
      《type》⟨te₁,te₂⟩,h ⊢ type_apply T ts ፥ SemTy.Substitute.substitute subst τ ▪

    | TAPP :
      《type》te,h ⊢ t₁ ፥ τ₁ ▪ →
      《type》te,h ⊢ t₂ ፥ τ₂ ▪ →
      ----------------------------------------------------------------------
      《type》te,h ⊢ Source.TypeExpression.app t₁ t₂ ፥ SemTy.TypeS.App τ₁ τ₂ ▪

  inductive types : Env.TE → Int
                  → List Source.TypeExpression
                  → List SemTy.TypeS
                  → Prop where
    | NIL :
      -------------------------
      《types》te,h ⊢ [] ፥ [] ▪

    | CONS :
      《types》te,h ⊢ ts ፥ τs ▪ →
      《type》 te,h ⊢ t  ፥ τ ▪ →
      -----------------------------------
      《types》te,h ⊢ t :: ts ፥ τ :: τs ▪
end

/--
Cp. Fig 25
```text
CE, TE, h ⊢ class : Γ τ
```
Checking a single typeclass constraint in a qualified type signature.
These constraints have the general form `C (u t₁ … tₙ)` where `C` is the name
of a typeclass, `u` is a type variable and `tᵢ` are types.
An example would be `Num (f Int Int)`.

-/
inductive classR : Env.CE → Env.TE → Int
                 → Source.ClassAssertion
                 → SemTy.SClass_Name
                 → SemTy.TypeS
                 → Prop where
  | CLASS :
    (C, Env.CEEntry.mk Γ h' x α ie) ∈ ce →
    h' < h →
    《type》te, h'' ⊢ List.foldl Source.TypeExpression.app (Source.TypeExpression.var u) ts ፥ τ ▪ →
    ------------------------------------------------------------------------------------------------
    《class》ce,te,h ⊢ Source.ClassAssertion.mk C u ts ፥ Γ , τ ▪

/--
Cp. Fig 25
```text
CE, TE, h ⊢ cx : θ
```
-/
inductive context : Env.CE → Env.TE → Int
                  → Source.Context
                  → SemTy.Context
                  → Prop where
  | CONTEXT :
    Forall3 class_assertions Γs τs (λ classᵢ Γᵢ τᵢ => 《class》ce,te,h ⊢ classᵢ ፥ Γᵢ ,τᵢ ▪) →
    -----------------------------------------------------------------------------------------
    《context》ce,te,h ⊢ class_assertions ፥ List.zip Γs τs ▪

/--
Cp. Fig 24
```text
GE ⊢ sig : VE
```
-/
inductive sig : Env.GE
              → Source.Signature
              → Env.VE
              → Prop where
  | SIG :
    ke = Env.kindsOf ce te →
    MinKindEnv ke_min (λ ke' => 《oplus》ke ⊞ ke' ≡ ke_sum ▪ ∧
                                《ktype》ke_sum ⊢ t ፥ SemTy.Kind.Star ▪ ∧
                                 (∀ ca ∈ cx, 《kclassassertion》ke_sum ⊢ ca ▪ )) →
    《context》_,_,_ ⊢ cx ፥ θ ▪ →
    《type》_,_ ⊢ t ፥ τ ▪ →
    /- fv(cx) ⊆ fv(t) → -/
    ---------------------------------------------------------
    《sig》⟨ce,te,de⟩ ⊢ (Source.Signature.mk v cx t) ፥ [⟨v,_⟩] ▪

/--
Cp. Fig 24
```text
GE ⊢ sigs : VE
```
-/
inductive sigs : Env.GE
               → List Source.Signature
               → Env.VE
               → Prop where
  | SIGS :
    Forall2 sgs ves (λ sg ve =>《sig》ge ⊢ sg ፥ ve ▪) →
    《oplus*》⊞{ ves }≡ ve ▪ →
    ---------------------------------------------------
    《sigs》ge ⊢ sgs ፥ ve ▪
