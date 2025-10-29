import HaskellSpec.SemanticTypes
import HaskellSpec.Source.Lang
import HaskellSpec.Source.Module
import HaskellSpec.Environments
import HaskellSpec.Forall2

/-!
# Kind System

The rules are defined in fig. 8, 9, 10 of the paper.
-/

namespace Kinding

set_option quotPrecheck false in
set_option hygiene false in
notation  "《kindord》" κ₁ "≼" κ₂ "▪" => KindOrdering κ₁ κ₂

/--
Defined in section 3.1.1
-/
inductive KindOrdering : SemTy.Kind
                       → SemTy.Kind
                       → Prop where
  | STAR_LT :
    -------------------------------
    《kindord》SemTy.Kind.Star ≼ κ ▪

  | FUN_CONG :
    《kindord》κ₁ ≼ κ₁' ▪ →
    《kindord》κ₂ ≼ κ₂' ▪ →
    ------------------------------------------------------------
    《kindord》SemTy.Kind.Fun κ₁ κ₂ ≼ SemTy.Kind.Fun κ₁' κ₂' ▪

theorem kind_ord_reflexive : ∀ κ, 《kindord》 κ ≼ κ ▪ := by
  intros κ
  induction κ with
  | Star => apply KindOrdering.STAR_LT
  | Fun κ₁ κ₂ IH₁ IH₂ => apply KindOrdering.FUN_CONG <;> assumption

theorem kind_ord_transitive : ∀ κ₁ κ₂ κ₃,
  《kindord》κ₁ ≼ κ₂ ▪ →
  《kindord》κ₂ ≼ κ₃ ▪ →
  《kindord》κ₁ ≼ κ₃ ▪ := by
  intros κ₁ κ₂ ; revert κ₁
  induction κ₂ with
  | Star =>
    intros κ₁ κ₃ H₁ H₂
    cases H₁ with
    | STAR_LT => apply KindOrdering.STAR_LT
  | Fun κ₂₁ κ₂₂ IH₁ IH₂ =>
    intros κ₁ κ₃ H₁ H₂
    cases H₁ with
    | STAR_LT => apply KindOrdering.STAR_LT
    | FUN_CONG HX₁ HX₂ =>
      cases H₂ with
      | FUN_CONG HX₃ HX₄ =>
        apply KindOrdering.FUN_CONG
        . apply IH₁ <;> assumption
        . apply IH₂ <;> assumption

theorem kind_ord_asymm : ∀ κ₁ κ₂,
  《kindord》κ₁ ≼ κ₂ ▪ →
  《kindord》κ₂ ≼ κ₁ ▪ →
  κ₁ = κ₂ := by
  intros κ₁
  induction κ₁ with
  | Star =>
    intros κ₂ H₁ H₂
    cases H₂ with
    | STAR_LT => rfl
  | Fun κ₁₁ κ₁₂ IH₁ IH₂ =>
    intros κ₂ H₁ H₂
    cases H₁ with
    | FUN_CONG HX₁ HX₂ =>
      cases H₂ with
      | FUN_CONG HX₃ HX₄ =>
        specialize IH₁ _ HX₁ HX₃
        specialize IH₂ _ HX₂ HX₄
        rw [IH₁, IH₂]

def decide_kind_ord (κ₁ κ₂ : SemTy.Kind) : Decidable 《kindord》κ₁ ≼ κ₂ ▪ :=
  match κ₁ with
  | SemTy.Kind.Star => by
    apply Decidable.isTrue
    apply KindOrdering.STAR_LT
  | SemTy.Fun κ₁₁ κ₁₂ =>
    match κ₂ with
    | SemTy.Kind.Star => by
      apply Decidable.isFalse
      intros HX
      cases HX
    | SemTy.Fun κ₂₁ κ₂₂ =>
      match decide_kind_ord κ₁₁ κ₂₁ with
      | Decidable.isFalse H => by
        apply Decidable.isFalse
        intros HX
        cases HX with
        | FUN_CONG => apply H ; assumption
      | Decidable.isTrue H₁ =>
        match decide_kind_ord κ₁₂ κ₂₂ with
        | Decidable.isFalse H => by
          apply Decidable.isFalse
          intros HX
          cases HX with
          | FUN_CONG => apply H ; assumption
        | Decidable.isTrue H₂ => by
          apply Decidable.isTrue
          apply KindOrdering.FUN_CONG <;> assumption

instance decidable_kind_ord {κ₁ κ₂ : SemTy.Kind }: Decidable 《kindord》κ₁ ≼ κ₂ ▪ :=
  decide_kind_ord κ₁ κ₂

def KindEnvOrdering (ke₁ ke₂ : Env.KE) : Prop :=
  sorry
  --∀ x ∈ ke₁, ∃ x' ∈ ke₂, x.fst = x'.fst ∧ 《kindord》 x.snd ≼ x'.snd ▪

notation  "《kindenvord》" ke₁ "≼" ke₂ "▪" => KindEnvOrdering ke₁ ke₂

/--
If `MinKindEnv ke_min f` holds, then `ke_min` is the smallest kind environment satisfying `f`.
This is used to implement kind defaulting.
-/
def MinKindEnv (ke : Env.KE) (f : Env.KE → Prop) : Prop :=
  f ke
  ∧
  (∀ ke', f ke → 《kindenvord》 ke ≼ ke' ▪)


set_option quotPrecheck false in
set_option hygiene false in
notation  "《ktype》" ke "⊢" t "፥" κ "▪"=> ktype ke t κ

/--
Fig. 10 (Kind inference, type expressions)
```text
KE ⊢ t : κ
```
-/
inductive ktype : Env.KE
                → Source.TypeExpression
                → SemTy.Kind
                → Prop where
  | KIND_TVAR :
    (u, κ) ∈ ke.ke₂ →
    ----------------------------------------------
    《ktype》ke ⊢ Source.TypeExpression.var u ፥ κ ▪

  | KIND_TCON :
    (T, κ) ∈ ke.ke₁ →
    ----------------------------------------------
    《ktype》ke ⊢ Source.TypeExpression.typename T ፥ κ ▪

  | KIND_APP :
    《ktype》ke ⊢ t₁ ፥ SemTy.Fun κ₁ κ₂ ▪ →
    《ktype》ke ⊢ t₂ ፥ κ₁ ▪ →
    ---------------------------------------------
    《ktype》ke ⊢ Source.TypeExpression.app t₁ t₂ ፥ κ₂ ▪


set_option quotPrecheck false in
set_option hygiene false in
notation  "《kclassassertion》" ke "⊢" ca "▪"=> kclassassertion ke ca

inductive kclassassertion : Env.KE
                          → Source.ClassAssertion
                          → Prop where
  | KIND_CLASS_ASSERTION :
    (ca.name, κ) ∈ ke.ke₃ →
    《ktype》ke ⊢ Source.classAssertionType ca ፥ κ ▪ →
    --------------------------------------------------
    kclassassertion ke ca

set_option quotPrecheck false in
set_option hygiene false in
notation  "《ksig》" ke "⊢" sig "▪"=> ksig ke sig

/--
Cp. fig 9
```text
KE ⊢ sig
```
-/
inductive ksig : Env.KE
               → Source.Signature
               → Prop where
  | KIND_SIG :
     (∀ e ∈ ke'.ke₂, ∃ u, e.fst = u) →
    《oplus》ke ⊞ ke' ≡ ke'' ▪ →
     (∀ ca ∈ cx, 《kclassassertion》ke'' ⊢ ca ▪ ) →
    《ktype》 ke'' ⊢ t ፥ SemTy.Kind.Star ▪ →
    -----------------------------------------------------
    《ksig》 ke ⊢ Source.Signature.mk v cx t ▪

set_option quotPrecheck false in
set_option hygiene false in
notation  "《kconDecl》" ke "⊢" condecl "▪"=> kconDecl ke condecl

/--
Cp. fig 9
```text
KE ⊢ conDecl
```
-/
inductive kconDecl : Env.KE
                   → Source.ConstructorDecl
                   → Prop where
  | KIND_POSCON :
    (∀ τ, τ ∈ tys → 《ktype》 ke ⊢ τ ፥ SemTy.Kind.Star ▪) →
    -------------------------------------------------------
    《kconDecl》 ke ⊢ Source.ConstructorDecl.poscon c tys ▪

  | KIND_LABCON :
    (∀ l τ, (l,τ) ∈ lbls → 《ktype》ke ⊢ τ ፥ SemTy.Kind.Star ▪) →
    --------------------------------------------------------
    《kconDecl》 ke ⊢ Source.ConstructorDecl.labcon c lbls ▪

set_option quotPrecheck false in
set_option hygiene false in
notation  "《kctDecl》" ke "⊢" kctdecl "፥" ke' "▪"=> kctDecl ke kctdecl ke'

/--
Cp. fig 8
```text
KE ⊢ ctDecl : KE
```
-/
inductive kctDecl : Env.KE
                  → Source.ClassOrType
                  → Env.KE
                  → Prop where
  | KIND_DATA :
     κ = SemTy.kind_fun_list κs →
     List.length κs = List.length us →
     ke''' = Env.KE.mk [] (List.zip us κs) [] →
    《oplus》ke ⊞  ke''' ≡ ke'' ▪ →
    (∀ ca ∈ cx, 《kclassassertion》 ke'' ⊢ ca ▪)→
    (∀ conDecl ∈  cons,《kconDecl》 ke'' ⊢ conDecl ▪) →
    ke_out = Env.KE.mk [⟨QType_Name.Unqualified S,κ⟩] [] [] →
    -----------------------------------------------------------
    《kctDecl》 ke ⊢ (Source.ClassOrType.ct_data cx S us cons) ፥ ke_out ▪

  | KIND_TYPE :
     List.length κs = List.length us →
     ke''' = Env.KE.mk [] (List.zip us κs) [] →
    《oplus》ke ⊞ ke''' ≡ ke'' ▪ →
    《ktype》 ke'' ⊢ t ፥ κ ▪ →
    κ_res = SemTy.kind_fun_list (κs ++ [κ]) →
    ke_out = Env.KE.mk [⟨QType_Name.Unqualified S,κ_res⟩] [] [] →
    ---------------------------------------------------------------
    《kctDecl》ke ⊢ Source.ClassOrType.ct_type S us t ፥ ke_out ▪

  | KIND_CLASS :
    《oplus》ke ⊞ Env.KE.mk [] [⟨u,κ⟩] [] ≡ ke' ▪ →
    (∀ ca ∈ cx, 《kclassassertion》ke' ⊢ ca ▪ )→
    (∀ sig ∈ sigs, 《ksig》ke' ⊢ sig ▪ ) →
    ke_out = Env.KE.mk [] [] [⟨QClassName.Unqualified B,κ⟩] →
    -----------------------------------------------------------
    《kctDecl》ke ⊢ Source.ClassOrType.ct_class cx B u sigs b ፥ ke_out ▪


set_option quotPrecheck false in
set_option hygiene false in
notation  "《kgroup》" ke "⊢" classortypes "፥" ke' "▪"=> kgroup ke classortypes ke'
/--
Cp. fig 8
```text
KE ⊢ ctDecl₁; … ; ctDeclₙ : KE
```
-/
inductive kgroup : Env.KE
                 → NonEmpty Source.ClassOrType
                 → Env.KE
                 → Prop where
  | KGROUP :
    Forall2NE class_or_types kes (λ ctDecl keᵢ => 《kctDecl》 ke ⊢ ctDecl ፥ keᵢ ▪) →
    《oplus*》⊞{ toList kes }≡ ke_res ▪ →
    -----------------------------------
    《kgroup》ke ⊢ class_or_types ፥ ke_res ▪


set_option quotPrecheck false in
set_option hygiene false in
notation  "《kctDecls》" ke "⊢" classandtypes "፥" ke' "▪"=> kctDecls ke classandtypes ke'

/--
Cp. fig 8
```text
KE ⊢ ctDecls : KE
```
-/
inductive kctDecls : Env.KE
                   → Source.ClassesAndTypes
                   → Env.KE
                   → Prop where
  | KCTDECLS :
    MinKindEnv ke_decls (λ ke' => ∃ ke'', 《oplus》ke ⊞ ke' ≡ ke'' ▪ ∧
                                           《kgroup》 ke'' ⊢ grp ፥ ke' ▪) →
    《oplus》ke ⊞ ke_decls ≡ ke_res ▪ →
    《kctDecls》 ke_res ⊢ rest ፥ ke_groups ▪ →
    《oplus》ke_decls ⊞ ke_groups ≡ ke_final ▪ →
    -----------------------------------------------------
    《kctDecls》ke ⊢ Source.ClassesAndTypes.decls grp rest ፥ ke_final ▪

  | KCTEMPTY :
    -------------------------------------------
    《kctDecls》 ke ⊢ Source.ClassesAndTypes.empty ፥ Env.KE.mk [] [] [] ▪

end Kinding
