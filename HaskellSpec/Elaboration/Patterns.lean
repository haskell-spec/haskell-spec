import HaskellSpec.Target.Lang
import HaskellSpec.Prelude
import HaskellSpec.Elaboration.Literals
import HaskellSpec.Source.Patterns

def unqual_var (var : Names.QVariable) : Names.Variable :=
  match var with
    | (Names.QVariable.Qualified _m x) => x
    | (Names.QVariable.Unqualified x) => x

/- Applying typeclass methods to their type, dictionary, and term arguments. -/

/- Prelude.== τ ed e -/
def apply_equals : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression := λ τ ed e =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.equals) (NonEmpty.mk τ [])
  Target.apps e' [ed, e]

/- Prelude!enumFromThenTo τ e e1' e2' e3' -/
def apply_enumFromThenTo : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression  → Target.Expression → Target.Expression :=
  λ τ e e1' e2' e3' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_then_to) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2', e3']

/- Prelude!enumFromTo τ e e1' e2' -/
def apply_enumFromTo : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression → Target.Expression :=
  λ τ e e1' e2' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_to) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2']

/- Prelude!enumFromThen τ e e1' e2' -/
def apply_enumFromThen : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression → Target.Expression :=
  λ τ e e1' e2' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_then) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2']

/- Prelude!enumFrom τ e e1' -/
def apply_enumFrom : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression :=
  λ τ e e1' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from) (NonEmpty.mk τ [])
  Target.apps e' [e, e1']


set_option quotPrecheck false in
set_option hygiene false in
notation  "《pat》" ge "," ie "⊢" s "⇝" t "፥" ve "," τ "▪" => pat ge ie s t ve τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《pats》" ge "," ie "⊢" ss "⇝" ts "፥" ve "," τ "▪" => pats ge ie ss ts ve τ

/-
Cp. Fig 43. 44.
```
GE, IE ⊢ p ⇝ p : VE, τ
```
-/

mutual
  inductive pat : Env.GE
                → Env.IE
                → Source.Pattern
                → Target.Pattern
                → Env.VE
                → SemTy.TypeS
                → Prop where
    | PVAR :
      σ = (SemTy.TypeScheme.Forall [] [] τ) →
      -----------------------------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.var x ⇝ Target.Pattern.var (unqual_var x) σ ፥ [(x, Env.VE_Item.Ordinary x σ)] , τ ▪

    | PAS :
      《pat》ge,ie ⊢ p ⇝ p' ፥ veₚ , τ ▪ →
      σ = SemTy.TypeScheme.Forall [] [] τ →
      《oplus》veₚ ⊞ [⟨v,Env.VE_Item.Ordinary v σ⟩] ≡ ve_res ▪ →
      -----------
      《pat》ge,ie ⊢ Source.Pattern.as v p ⇝ Target.Pattern.as v σ p' ፥ ve_res , τ ▪

    | PIRR :
      《pat》ge,ie ⊢ p₁ ⇝ p₂ ፥ ve, τ ▪ →
      -----------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.lazy p₁ ⇝ Target.Pattern.lazy p₂ ፥ ve, τ ▪

    | PWILD :
      --------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.wildcard ⇝ Target.Pattern.wildcard ፥ [], τ ▪

    | PCON :
      ge = ⟨ce,te,⟨de₁,de₂⟩⟩ →
      ⟨K,⟨K,χ,SemTy.TypeScheme.Forall αs θ _⟩⟩ ∈ de₁ →
      《pats》ge,ie ⊢ ps ⇝ ps' ፥ ves , τs ▪ →
      《oplus*》⊞{ ves }≡ ve_res ▪ →
      《dict》ie ⊢ e ፥ θ ▪ → -- TODO: subst for datatype contexts
      τ = SemTy.type_apps (SemTy.TypeS.TypeConstructor χ) τs' →
      ------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.constructor c ps ⇝ Target.Pattern.constructor c ps' ፥ ve_res , τ ▪

    | PLAB :
      ge = ⟨ce,te,⟨de₁,de₂⟩⟩ →
      -------------------------------
      《pat》ge,ie ⊢ Source.Pattern.constructor_labelled c lps ⇝ Target.Pattern.constructor_labelled c lps' ፥ _ , _ ▪

    | PCHAR :
      -------------------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.literal (Source.Literal.char c) ⇝ Target.Pattern.char c ፥ [],Prelude.char ▪

    | PSTRING :
      ---------------------------------------------------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.literal (Source.Literal.string s) ⇝ Target.Pattern.string s ፥ [], Prelude.mk_list Prelude.char ▪

    | PINTEGER :
      《literal》 ie ⊢ (Source.Literal.integer i) ⇝ e ፥ τ ▪  →
      《dict》 ie ⊢ ed ፥ [⟨Prelude.eq, τ⟩] ▪ →
      -----------------------------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.literal (Source.Literal.integer i) ⇝ Target.Pattern.exp (apply_equals τ ed e) ፥ [], τ ▪

    | PFLOAT :
      《literal》 ie ⊢ (Source.Literal.float n d) ⇝ e ፥ τ ▪ →
      《dict》 ie ⊢ ed ፥ [⟨Prelude.eq, τ⟩] ▪ →
      -----------------------------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.literal (Source.Literal.float n d) ⇝ Target.Pattern.exp (apply_equals τ ed e) ፥ [], τ ▪

  inductive pats : Env.GE
                 → Env.IE
                 → List Source.Pattern
                 → List Target.Pattern
                 → List Env.VE
                 → List SemTy.TypeS
                 → Prop where
  | NIL :
    ----------------------------------
    《pats》ge,ie ⊢ [] ⇝ [] ፥ [], [] ▪

  | CONS :
    《pat》ge,ie ⊢ p ⇝ p' ፥ ve, τ ▪ →
    《pats》ge,ie ⊢ ps ⇝ ps' ፥ ves, τs ▪ →
    --------------------------------------------------
    《pats》ge,ie ⊢ p::ps ⇝ p'::ps' ፥ ve::ves, τ::τs ▪
end
