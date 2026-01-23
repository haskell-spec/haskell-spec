import HaskellSpec.Target.Lang
import HaskellSpec.Prelude
import HaskellSpec.Elaboration.Literals
import HaskellSpec.Source.Patterns
import HaskellSpec.Names

/- Applying typeclass methods to their type, dictionary, and term arguments. -/

/-- Helper function to construct the target expression `Prelude.== τ ed e` -/
def apply_equals : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression := λ τ ed e =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.equals) (NonEmpty.mk τ [])
  Target.apps e' [ed, e]

/-- Helper function to construct the target expression `Prelude!enumFromThenTo τ e e1' e2' e3'` -/
def apply_enumFromThenTo : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression  → Target.Expression → Target.Expression :=
  λ τ e e1' e2' e3' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_then_to) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2', e3']

/-- Helper function to construct the target expression `Prelude!enumFromTo τ e e1' e2'` -/
def apply_enumFromTo : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression → Target.Expression :=
  λ τ e e1' e2' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_to) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2']

/-- Helper function to construct the target expression `Prelude!enumFromThen τ e e1' e2'` -/
def apply_enumFromThen : SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression → Target.Expression :=
  λ τ e e1' e2' =>
  let e' := Target.Expression.typ_app (Target.Expression.var Prelude.enum_from_then) (NonEmpty.mk τ [])
  Target.apps e' [e, e1', e2']

/-- Helper function to construct the target expression `Prelude!enumFrom τ e e1'` -/
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
  /--
  This judgement elaborates a pattern from the source language to a pattern from
  the target language and additionally yields:
  - A variable environment which gives the types of the variables which occur
    in the pattern.
  - The type that the pattern matches against.
  -/
  inductive pat : Env.GE
                → Env.IE
                → Source.Pattern
                → Target.Pattern
                → Env.VE
                → SemTy.TypeS
                → Prop where
      /--
      Faxen adds the following note for this rule at the beginning of section 9:

      "For the benefit of method bindings in instance declarations, the abstract
       syntax of patterns and the PVAR rule allow single variables to be qualified.
       The translated pattern is still unqualified but the returned environment
       associates the type with the qualified name since it is checked against the
       (possibly imported) variable in the INST rule [..]. Variables also occur in
       as-patterns `v@p` [..] where only unqualified variables are allowed."
      -/
    | PVAR :
      σ = (SemTy.TypeScheme.Forall [] [] τ) →
      env = [(x, Env.VE_Item.Ordinary x σ)] →
      -------------------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.var x ⇝ Target.Pattern.var (Names.unqual_var x) σ ፥ env , τ ▪

    | PAS :
      《pat》ge,ie ⊢ p ⇝ p' ፥ veₚ , τ ▪ →
      σ = SemTy.TypeScheme.Forall [] [] τ →
      ve_ext = [⟨Names.QVariable.Unqualified v, Env.VE_Item.Ordinary (Names.QVariable.Unqualified v) σ⟩] →
      《oplus》veₚ ⊞ ve_ext ≡ ve_res ▪ →
      ------------------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.as v p ⇝ Target.Pattern.as v σ p' ፥ ve_res , τ ▪

    | PIRR :
      《pat》ge,ie ⊢ p ⇝ p' ፥ ve, τ ▪ →
      -----------------------------------------------------------------------
      《pat》ge,ie ⊢ Source.Pattern.lazy p ⇝ Target.Pattern.lazy p' ፥ ve, τ ▪

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
      《pats》ge,ie ⊢ _ ⇝ _ ፥ _ , _ ▪ →
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

  /--
  This judgement elaborates a list of source patterns to a list of target patterns, variable environments and types.
  -/
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
