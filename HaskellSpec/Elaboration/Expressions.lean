import HaskellSpec.Environments
import HaskellSpec.Forall2
import HaskellSpec.Source.Lang
import HaskellSpec.Source.Patterns
import HaskellSpec.Source.Literals
import HaskellSpec.Target.Lang
import HaskellSpec.SemanticTypes
import HaskellSpec.Elaboration.Dictionary
import HaskellSpec.Elaboration.Literals
import HaskellSpec.Elaboration.Patterns
import HaskellSpec.Elaboration.Types
import HaskellSpec.NonEmpty
import HaskellSpec.Prelude


/- Prelude!(>>) τ ed ed τ₁ τ₂ e₁ e₂ -/
def apply_sequence : SemTy.TypeS → Target.Expression → SemTy.TypeS → SemTy.TypeS → Target.Expression → Target.Expression → Target.Expression :=
  λ τ ed τ₁ τ₂ e₁ e₂ =>
  let e'   := Target.Expression.typ_app (Target.Expression.var Prelude.sequence) (NonEmpty.mk τ [])
  let e''  := Target.apps e' [ed]
  let e''' := Target.Expression.typ_app e'' (NonEmpty.mk τ₁ [τ₂])
  Target.apps e''' [e₁,e₂]

def concat_target_binds (n m: Target.Binds): Target.Binds :=
  -- TODO Looks like Target.Binds isn't completely
  -- defined yet. But when it is, we should define
  -- this.
  sorry


set_option quotPrecheck false in
set_option hygiene false in
notation  "《bindG》" ge "," ie "," ve "⊢" sgs ";" bs "⇝" bs' "፥" ve' "▪" => bindG ge ie ve sgs bs bs' ve'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《binds》" ge "," ie "," ve "⊢" bs "⇝" bs' "፥" ve' "▪" => binds ge ie ve bs bs' ve'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《exp》" ge "," ie "," ve "⊢" e "⇝" e' "፥" τ "▪" => exp ge ie ve e e' τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《exps》" ge "," ie "," ve "⊢" es "⇝" es' "፥" τs "▪" => exps ge ie ve es es' τs

set_option quotPrecheck false in
set_option hygiene false in
notation  "《quals》" ge "," ie "," ve "⊢" q "⇝" q' "፥" ve' "▪" => quals ge ie ve q q' ve'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《stmts》" ge "," ie "," ve "⊢" s "⇝" e "፥" τ "▪" => stmts ge ie ve s e τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《gde》" ge "," ie "," ve "⊢" gde' "⇝" gde'' "፥" τ "▪" => gde ge ie ve gde' gde'' τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《gdes》" ge "," ie "," ve "⊢" gdes' "⇝" gdes'' "፥" τ "▪" => gdes ge ie ve gdes' gdes'' τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《match》" ge "," ie "," ve "⊢" match' "⇝" match'' "፥" τ "▪" => matchR ge ie ve match' match'' τ

set_option quotPrecheck false in
set_option hygiene false in
notation  "《bind》" ge "," ie "," ve "⊢" bind' "⇝" bind'' "፥" ve' "▪" => bind ge ie ve bind' bind'' ve'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《monobinds》" ge "," ie "," ve "⊢" bs "⇝" bs' "፥" ve' "▪" => monobinds ge ie ve bs bs' ve'

mutual
  /--
  Qualifiers appear on the right side of list comprehensions: `[e | qual₁, …, qualₙ]` and can bring additional
  variables into scope that can be used in the expression `e` and other qualifiers to the right.

  The judgement `《quals》ge,ie,ve_in ⊢ qual ⇝ qual' ፥ ve_out ▪` means that in the context `ge,ie,ve_in` we can elaborate
  the source qualifier `qual` to the target qualifier `qual'`.

  The context `ve_in` is the combination of the variable context from without the list comprehension and the bindings
  introduced by the qualifiers to the left of the one we are currently checking.

  The context `ve_out` only contains those variable bindings introduced by the list of qualifiers, and not the bindings
  from without the list comprehension.

  (Defined in Fig. 40 of Faxen)
  -/
  inductive quals : Env.GE → Env.IE → Env.VE
                  → Source.Qualifiers
                  → Target.Qualifiers
                  → Env.VE
                  → Prop where
      /--
      We typecheck a qualifier `[_ |…, p <- e, qs]`.

      We have to check the expression `e` in the context `ve_in` which has to result in some list type `[τ]`.
      We then have to check the pattern `p` against the type `τ` and extend the local context bound by the pattern.

      Variables bound in `qs` shadow variables bound in `p`.
      -/
    | QGEN :
      《exp》  ge,ie,ve_in     ⊢ e  ⇝ e'  ፥ Prelude.mk_list τ ▪ →
      《pat》  ge,ie           ⊢ p  ⇝ p'  ፥ ve_pattern, τ ▪ →
      ve_middle = Env.oplusarrow ve_in ve_pattern →
      《quals》ge,ie,ve_middle ⊢ qs ⇝ qs' ፥ ve_quals ▪ →
      ve_out = Env.oplusarrow ve_p ve_quals →
      ------------------------------------------------------------------------------------------------------------
      《quals》ge,ie,ve_in ⊢ Source.Qualifiers.list_bind p e qs ⇝ Target.Qualifiers.list_bind p' e' qs' ፥ ve_out ▪

      /--
      We typecheck a qualifier `[_ |…, let binds, qs]`.
      -/
    | QLET :
      《binds》ge,ie,ve_in      ⊢ bs ⇝ bs' ፥ ve_binds ▪ →
      ve_middle = Env.oplusarrow ve_in ve_binds →
      《quals》ge,ie, ve_middle ⊢ qs ⇝ qs' ፥ ve_quals ▪ →
      ve_out = Env.oplusarrow ve_binds ve_quals →
      -------------------------------------------------------------------------------------------------
      《quals》ge,ie,ve_in ⊢ Source.Qualifiers.lbind bs qs ⇝ Target.Qualifiers.lbind bs' qs' ፥ ve_out ▪

      /--
      We typecheck a qualifier `[_ | …, e , qs]`.

      We have to check that the expression `e` has type `Bool` in the context `ve_in`.
      No new variables are brought into scope.
      -/
    | QFILTER :
     《exp》  ge,ie,ve_in ⊢ e  ⇝ e'  ፥ Prelude.bool ▪ →
     《quals》ge,ie,ve_in ⊢ qs ⇝ qs' ፥ ve_out ▪ →
     -----------------------------------------------------------------------------------------------
     《quals》ge,ie,ve_in ⊢ Source.Qualifiers.guard e qs ⇝ Target.Qualifiers.guard e' qs' ፥ ve_out ▪

      /--
      The output environment `ve_out` should not contain variables introduced in the outer scope.
      We therefore have to return an empty environment here.
      -/
    | QEMPTY :
     ----------------------------------------------------------------------------
     《quals》ge,ie,ve ⊢ Source.Qualifiers.empty ⇝ Target.Qualifiers.empty ፥ [] ▪

  /--
  The central elaboration judgement for expressions.

  The judgement `《exp》ge,ie,ve ⊢ e ⇝ e' ፥ τ` means that in the environment `ge,ie,ve` we can
  elaborate the source expression `e` to the target expression  `e'` and check that it has the
  semantic mono-type `τ`.

  (Defined in Fig. 36, 38, 39 and 42 of Faxen)
  -/
  inductive exp : Env.GE → Env.IE → Env.VE
                → Source.Expression
                → Target.Expression
                → SemTy.TypeS
                → Prop where
      /--
      A variable `x` with a type scheme `∀ αs. θ => τ` that has been introduced at a variable binding site or as a
      record field access.

      We need to find a substitution `[τs/αs]` which maps type variables `αs` to concrete types `τs`.
      We create a typeclass dictionary `ed` for the constraint `θ[τs/αs]` and elaborate the variable `x`
      by applying it to the types and the dictionary: `x τs ed`.
      The resulting expression has the type `τ[τs/αs]`.
      -/
    | VAR_1 :
      ⟨x, (Env.VE_Item.Ordinary x (SemTy.TypeScheme.Forall αs θ τ))⟩ ∈ ve →
      Env.dom τsForαs = αs →
      《dict》 ie ⊢ ed ፥ SemTy.Substitute.substitute τsForαs θ ▪ →
      e_target = Target.Expression.app (Target.typ_app_ (Target.Expression.var x) (Env.rng τsForαs)) ed →
      ---------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.var x ⇝ e_target ፥ SemTy.Substitute.substitute τsForαs τ ▪

      /--
      A variable `x` that has been introduced as a typeclass method.
      Typeclass methods have a more complicated type scheme `∀ β, Γ ⇒ ∀ αs, θ => τ`.

      The function  `(>>=)`, for example, has type `∀m, Monad m => ∀a b, m a -> (a -> m b) -> m b`.
      In this example the context `θ` is empty.
      -/
    | VAR_2 :
      ⟨x, (Env.VE_Item.Class x (SemTy.ClassTypeScheme.Forall β Γ (SemTy.TypeScheme.Forall αs θ τ) ))⟩ ∈ ve →
      《dict》 ie ⊢ e1 ፥ [(Γ, τ)] ▪ →
      Env.dom τsForαs = αs →
      《dict》 ie ⊢ e2 ፥ SemTy.Substitute.substitute τsForαs θ ▪ →
      e_target = Target.Expression.app (Target.typ_app_ (Target.Expression.app (Target.Expression.typ_app (Target.Expression.var x) (singleton τ)) e1) (Env.rng τsForαs)) e2 →
      --------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.var x ⇝ e_target ፥ SemTy.Substitute.substitute (List.cons (β, τ) τsForαs) τ ▪

      /--
      A literal is elaborated using the judgement form `《literal》`.
      -/
    | LITERAL :
      《literal》  ie ⊢ lit ⇝ e ፥ τ ▪ →
      ------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.lit lit ⇝ e ፥ τ ▪

    | LAMBDA :
      Forall4NE ps ps' ves τs (λ p p' ve' τ' => 《pat》ge,ie ⊢ p ⇝ p' ፥ ve', τ' ▪) →
      《exp》ge,ie,_ ⊢ e ⇝ e' ፥ τ ▪ →
      ---------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.abs ps e ⇝ Target.Expression.abs ps' e' ፥ _ ▪

      /--
      In order to check the function application `e₁ e₂` we need to check that `e₁` has
      a function type `τ' → τ` and that `e₂` has type `τ'`.
      -/
    | APP :
      《exp》ge,ie,ve ⊢ e₁ ⇝ e₁' ፥ Prelude.mk_funt τ' τ ▪ →
      《exp》ge,ie,ve ⊢ e₂ ⇝ e₂' ፥ τ' ▪ →
      ----------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.app e₁ e₂ ⇝ Target.Expression.app e₁' e₂' ፥ τ ▪

      /--
      In order to check the expression `let bs in e` we have to first check the bindings `bs`
      and compute the extended environment `ve_extended` before checking `e`.
      -/
    | LET :
      《binds》ge,ie,ve ⊢ bs ⇝ bs' ፥ ve_binds ▪ →
      ve_extended = Env.oplusarrow ve ve_binds →
      《exp》ge,ie,ve_extended ⊢ e ⇝ e' ፥ τ ▪ →
      -------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.let_bind bs e ⇝ Target.Expression.let_bind bs' e' ፥ τ ▪

    | CASE :
      《exp》ge,ie,ve ⊢ e ⇝ e' ፥ τ' ▪ →
      /-Forall2NE ms ms' (λ m m' => matchR ge ie ve m m' (SemTy.TypeS.App (SemTy.TypeS.App SemTy.prelude_fun τ') τ)) → -/
      -----------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.case e ms ⇝ Target.Expression.case e' ms' ፥ τ ▪

      /--
      When typechecking a list comprehension `[e | quals]` we first check the qualifiers `quals` in order
      to obtain the list of variables `ve_quals` they bring into scope.
      We then typecheck `e` in the context extended with `ve_quals` to obtain the type `τ`.
      The entire list comprehension then has type `[τ]`.
      -/
    | LIST_COMP :
      《quals》ge,ie,ve                         ⊢ quals_source ⇝ quals_target ፥ ve_quals ▪ →
      《exp》  ge,ie,Env.oplusarrow ve ve_quals ⊢ e_source     ⇝ e_target     ፥ τ ▪ →
      -------------------------------------------------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.listComp e_source quals_source ⇝ Target.Expression.listComp e_target quals_target ፥ Prelude.mk_list τ ▪

      /--
      A do block `do {stmt₁,…,stmtₙ}` is elaborated using the judgement form `《stmts》`.
      -/
    | DO :
      《stmts》ge,ie,ve ⊢ s ⇝ e ፥ τ ▪ →
      --------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.do_block s ⇝ e ፥ τ ▪

      /--
      A constructor `K` has a typescheme `∀αs,θ => τ` in the environment due to datatype contexts.
      We therefore have to create a typeclass dictionary `ed` for the instance `θ[τs/αs]` even though
      this dictionary is not used in the elaboration.

      We elaborate the constructor by applying it to appropriate type arguments: `K τs`.
      -/
    | CON :
      ge = ⟨ce,te,⟨de₁,de₂⟩⟩ →
      ⟨K,⟨K,χ,SemTy.TypeScheme.Forall αs θ τ⟩⟩ ∈ de₁ →
      Env.dom τsForαs = αs →
      《dict》ie ⊢ ed ፥ SemTy.Substitute.substitute τsForαs θ ▪ →
      e_target = Target.typ_app_ (Target.Expression.constr K) (Env.rng τsForαs) →
      ------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.constr K ⇝ e_target ፥ SemTy.Substitute.substitute τsForαs τ ▪

      /--
      A record update `e { lab₁ = e₁, … , labₙ = eₙ }`
      -/
    | UPD :
      ge = ⟨ce,te,⟨de₁,de₂⟩⟩ →
      《exp》ge,ie,ve ⊢ e ⇝ e' ፥ τ_old ▪ →
      《exps》ge,ie,ve ⊢ ups.map (λ x => x.snd) ⇝ es' ፥ τs ▪ →
      《lcon》ie,_ ⊢ τ_old,_,τ_new ▪ →
      ---------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.recUpd e ups ⇝  Target.Expression.recUpd e' _ ፥ τ_new ▪

      /--
      A constructor with labelled arguments `K { lab₁ = e₁, … , labₙ = eₙ }`
      -/
    | LABCON :
      ge = ⟨ce,te,⟨de₁,de₂⟩⟩ →
      《exps》ge,ie,ve ⊢ bs.map (λ x => x.snd) ⇝ es' ፥ τs ▪ →
      ⟨K,⟨K,χ,σ⟩⟩ ∈ de₁ →
      《lcon》ie,φ ⊢ _,_,τ ▪ →
      ∀ lab ∈ bs.map (λ x => x.fst), ⟨lab,⟨lab,_,le⟩⟩ ∈ de₂ →
      -----------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.recConstr K bs ⇝ Target.Expression.recConstr _ _ ፥ _ ▪

      /--
      For the arithmetic sequence `[e₁,e₂..e₃]` we check that `e₁`, `e₂` and `e₃` have some common type `τ`.
      We then generate a dictionary `ed` for `Enum τ` and elaborate the expression to `enumFromThenTo τ ed e₁ e₂ e₃`.
      -/
    | ENUM_FROM_THEN_TO :
      《exp》ge,ie,ve ⊢ e₁ ⇝ e₁' ፥ τ ▪ →
      《exp》ge,ie,ve ⊢ e₂ ⇝ e₂' ፥ τ ▪ →
      《exp》ge,ie,ve ⊢ e₃ ⇝ e₃' ፥ τ ▪ →
      《dict》     ie ⊢ ed ፥ [⟨Prelude.enum, τ⟩] ▪ →
      -------------------------------------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.listRange e₁ (some e₂) (some e₃) ⇝ apply_enumFromThenTo τ ed e₁' e₂' e₃' ፥ Prelude.mk_list τ ▪

      /--
      For the arithmetic sequence `[e₁..e₂]` we check that `e₁` and `e₂` have some common type `τ`.
      We then generate a dictionary `ed` for `Enum τ` and elaborate the expression to `enumFromTo τ ed e₁ e₂`.
      -/
    | ENUM_FROM_TO :
      《exp》ge,ie,ve ⊢ e₁ ⇝ e₁' ፥ τ ▪ →
      《exp》ge,ie,ve ⊢ e₂ ⇝ e₂' ፥ τ ▪ →
      《dict》     ie ⊢ ed ፥ [⟨Prelude.enum, τ⟩] ▪ →
      -------------------------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.listRange e₁ none (some e₂) ⇝ apply_enumFromTo τ ed e₁' e₂' ፥ Prelude.mk_list τ ▪

      /--
      For the arithmetic sequence `[e₁,e₂..]` we check that `e₁` and `e₂` have some common type `τ`.
      We then generate a dictionary `ed` for `Enum τ` and elaborate the expression to `enumFromThen τ ed e₁ e₂`.
      -/
    | ENUM_FROM_THEN :
      《exp》ge,ie,ve ⊢ e₁ ⇝ e₁' ፥ τ ▪ →
      《exp》ge,ie,ve ⊢ e₂ ⇝ e₂' ፥ τ ▪ →
      《dict》     ie ⊢ ed ፥ [⟨Prelude.enum, τ⟩]  ▪ →
      ---------------------------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.listRange e₁ (some e₂) none ⇝ apply_enumFromThen τ ed e₁' e₂' ፥ Prelude.mk_list τ ▪

      /--
      For the arithmetic sequence `[e₁..]` we check that `e₁` has some type `τ`.
      We then generate a dictionary `ed` for `Enum τ` and elaborate the expression to `enumFrom τ ed e₁`.
      -/
    | ENUM_FROM :
      《exp》ge,ie,ve ⊢ e₁ ⇝ e₁' ፥ τ ▪ →
      《dict》     ie ⊢ e ፥ [⟨Prelude.enum, τ⟩] ▪ →
      --------------------------------------------------------------------------------------------------------
      《exp》ge,ie,ve ⊢ Source.Expression.listRange e₁ none none ⇝ apply_enumFrom τ e e₁' ፥ Prelude.mk_list τ ▪

  inductive exps : Env.GE → Env.IE → Env.VE
                 → List Source.Expression
                 → List Target.Expression
                 → List SemTy.TypeS
                 → Prop where

  /--
  Statements appear within do blocks `do { stmt₁ ; … ; stmtₙ }`.

  The judgement `《stmts》ge,ie,ve ⊢ s ⇝ e ፥ τ` says that in the environment `ge,ie,ve` the source
  statements `s` can be elaborated to the target expression `e` of (monadic) type `τ`.

  (Defined in Fig. 41 of Faxen)
  -/
  inductive stmts : Env.GE → Env.IE → Env.VE
                  → Source.Statements
                  → Target.Expression
                  → SemTy.TypeS
                  → Prop where
      /--
      We typecheck a statement `do {… p <- e ; s}`.
      -/
    | SBIND :
      《exp》 ge,ie,ve ⊢ e ⇝ e₁ ፥ SemTy.TypeS.App τ τ₁ ▪ →
      《pat》    ge,ie ⊢ p ⇝ p' ፥ veₚ,  τ₁ ▪ →
      《stmts》ge,ie,_ ⊢ s ⇝ e₂ ፥ SemTy.TypeS.App τ τ₂ ▪ →
      《dict》      ie ⊢ ed ፥ [⟨Prelude.monad, τ⟩] ▪ →
      -----------------------------------------------------------------------------
      《stmts》ge,ie,ve ⊢ Source.Statements.mbind p e s ⇝ _ ፥ SemTy.TypeS.App τ τ₂ ▪

      /--
      We typecheck a statement `do {… let bs ; s}`.
      -/
    | SLET :
      《binds》ge,ie,ve ⊢ bs ⇝ bs' ፥ ve_binds ▪ →
      《stmts》ge,ie,Env.oplusarrow ve ve_binds ⊢ s ⇝ e ፥ τ ▪ →
      ----------------------------------------------------------------------------------------
      《stmts》ge,ie,ve ⊢ Source.Statements.lbind bs s ⇝ Target.Expression.let_bind bs' e ፥ τ ▪

      /--
      We typecheck a statement `do {… e ; s}`.
      -/
    | STHEN :
      《exp》  ge,ie,ve ⊢ e ⇝ e₁ ፥ SemTy.TypeS.App τ τ₁ ▪ →
      《stmts》ge,ie,ve ⊢ s ⇝ e₂ ፥ SemTy.TypeS.App τ τ₂ ▪ →
      《dict》       ie ⊢ ed ፥ [⟨Prelude.monad, τ⟩] ▪ →
      e' = apply_sequence τ ed τ₁ τ₂ e₁ e₂ →
      --------------------------------------------------------------------------
      《stmts》ge,ie,ve ⊢ Source.Statements.seq e s ⇝ e' ፥ SemTy.TypeS.App τ τ₂ ▪

      /--
      We typecheck a statement `do {… ; e}`.

      Note that this rule enforces a monad constraint but doesn't use the dictionary in the elaboration.
      GHC, on the other hand, allows to typecheck expressions like `do { 2 + 2 }` using a pure type like `Int`.
      -/
    | SRET :
      《exp》ge,ie,ve ⊢ e ⇝ e' ፥ SemTy.TypeS.App τ τ₁ ▪ →
      《dict》     ie ⊢ ed ፥ [⟨Prelude.monad, τ⟩] ▪ →
      -------------------------------------------------------------------
      《stmts》ge,ie,ve ⊢ Source.Statements.last e ⇝ e' ፥ SemTy.TypeS.App τ τ₁ ▪

  /--
  Cp. Fig 35
  ```text
  GE, IE, VE ⊢ gde ⇝ gde : τ
  ```
  -/
  inductive gde : Env.GE → Env.IE → Env.VE
                → Source.GuardedExp
                → Target.GuardedExp
                → SemTy.TypeS
                → Prop where
    | GDE :
      《exp》ge,ie,ve ⊢ e1 ⇝ e1' ፥ Prelude.bool ▪ →
      《exp》ge,ie,ve ⊢ e2 ⇝ e2' ፥ τ ▪ →
      ---------------------------------------------------------------------------------
      《gde》ge,ie,ve ⊢ Source.GuardedExp.mk e1 e2 ⇝ Target.GuardedExp.mk e1' e2' ፥ τ ▪

  /--
  Cp. Fig 35
  ```text
  GE, IE, VE ⊢ gdes ⇝ gdes : τ
  ```
  -/
  inductive gdes : Env.GE → Env.IE → Env.VE
                 → Source.GuardedExprs
                 → Target.GuardedExprs
                 → SemTy.TypeS
                 → Prop where
    | GDES :
      /- Forall2NE gs gs' (λ g g' => gde ge ie (Env.oplusarrow ve ve_binds) g g' τ) → -/
      《binds》ge,ie,ve ⊢ bs ⇝ bs' ፥ ve_binds ▪ →
      -------------------------------------------------------------------------------
      《gdes》ge,ie,ve ⊢ Source.GuardedExprs.mk gs bs ⇝ Target.GuardedExprs.mk gs' bs' ፥ τ ▪

  /--
  Cp. Fig 35
  ```text
  GE, IE, VE ⊢ match ⇝ match : τ
  ```
  -/
  inductive matchR : Env.GE
                   → Env.IE
                   → Env.VE
                   → Source.Match
                   → Target.Match
                   → SemTy.TypeS
                   → Prop where
    | MATCH :
      Forall3NE patts patts' ves (λ p p' ve' => 《pat》ge,ie ⊢ p ⇝ p' ፥ ve',τ ▪) →
      《gdes》ge,ie,_  ⊢ gs ⇝ gs' ፥ τ ▪ →
      -----------------------------------------------------------------------------
      《match》ge,ie,ve ⊢ Source.Match.mk patts gs ⇝ Target.Match.mk patts' gs' ፥ _ ▪

  /--
  Cp. Fig 34
  ```text
  GE, IE, VE ⊢ bind ⇝ bind : VE
  ```
  -/
  inductive bind : Env.GE → Env.IE → Env.VE
                 → Source.Binding
                 → Target.Binding
                 → Env.VE
                 → Prop where
    | FUNBIND :
      /- Forall2NE match_sources match_targets (λ match_sourceᵢ match_targetᵢ =>
      matchR ge ie ve match_sourceᵢ match_targetᵢ τ) → -/
      x = Names.QVariable.Unqualified (Names.Variable.Mk "x") →
      bind ge ie ve
        (Source.Binding.bind_match x match_sources)
        (Target.Binding.bind_match x match_targets)
        (List.singleton (Prod.mk x (Env.VE_Item.Ordinary x (SemTy.TypeScheme.Forall [] [] τ))))

    | PATBIND :
      《pat》ge,ie ⊢ p_source ⇝ p_target ፥ veₚ,  τ ▪ →
      《gdes》ge,ie,ve ⊢ gdes_source ⇝ gedes_target ፥ τ ▪ →
      bind ge ie ve (Source.Binding.bind_pat p_source gdes_source) (Target.Binding.bind_pat p_target gdes_target) veₚ

  /--
  Cp. Fig 34
  ```text
  GE, IE, VE ⊢ bindG ⇝ binds : VE
  ```
  -/
  inductive monobinds : Env.GE → Env.IE → Env.VE
                      → List Source.Binds
                      → Target.Binds
                      → Env.VE
                      → Prop where
    | MONOBINDS :
      -- Forall3 bs bs' ves (λ b b' veᵢ => 《bind》ge,ie,ve ⊢ b ⇝ b' ፥ veᵢ ▪ ) →
      ------------------------------------
      《monobinds》ge,ie,ve ⊢ _ ⇝ _ ፥ _ ▪

  /--
  Cp. Fig 30
  ```text
  GE, IE, VE ⊢ sigs;bindG ⇝ binds : VE
  ```
  -/
  inductive bindG : Env.GE → Env.IE → Env.VE
                  → List Source.Signature
                  → List Source.Binds
                  → Target.Binds
                  → Env.VE
                  → Prop where
    | BINDG :
      《sigs》ge ⊢ _ ፥ _ ▪ →
      《monobinds》 _,_,_ ⊢ _ ⇝ _ ፥ _ ▪ →
      -------------------------------
      《bindG》ge,_,_ ⊢ _ ; _ ⇝ _ ፥ _ ▪

  /--
  Cp. Fig. 29
  ```text
  GE, IE, VE ⊢ binds ⇝ binds : VE
  ```
  -/
  inductive binds : Env.GE → Env.IE → Env.VE
                  → Source.Binds
                  → Target.Binds
                  → Env.VE
                  → Prop where
    | BINDS :
      《bindG》ge,ie, ve                         ⊢ sgs ; bnds ⇝ binds' ፥ ve_bindg ▪ →
      《binds》ge,ie, Env.oplusarrow ve ve_bindg ⊢ bnds' ⇝ binds'' ፥ ve_binds ▪ →
      《oplus》ve_bindg ⊞ be_binds ≡ ve_res ▪ →
      --------------------------------------------------------------------------------------------------------------------------------------
      《binds》ge,ie,ve ⊢ Source.Binds.cons sgs bnds bnds' ⇝ concat_target_binds binds' binds'' ፥ ve_res ▪

    | EMPTY_BINDS :
      ------------------------------------------------------------------
      《binds》ge,ie,ve ⊢ Source.Binds.empty ⇝ Target.Binds.non_recursive [] ፥ [] ▪
end
