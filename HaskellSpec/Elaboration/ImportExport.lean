import HaskellSpec.Environments
import HaskellSpec.Source.Lang
import HaskellSpec.Source.Module
import HaskellSpec.Names
import HaskellSpec.Forall2


/-!
# Import + Export Declarations
-/

set_option quotPrecheck false in
set_option hygiene false in
notation  "《entity》" ee "⊢"  ent "፥" ee' "▪" => Entity ee ent ee'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《export》" fe "," se "⊢"  ent "፥" fe' "▪" => Export fe se ent fe'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《implist》" m "," ee "⊢"  implist "፥" ee' "▪" => Implist m ee implist ee'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《qualifier》" ee "⊢"  qualifier "፥" ee' "▪" => Qualifier ee qualifier ee'

set_option quotPrecheck false in
set_option hygiene false in
notation  "《import》" me "⊢"  imp "፥" fe "," se "▪" => Import me imp fe se

/--
Cp. Fig 14
```text
EE ⊢ ent, EE
```
-/
inductive Entity : Env.EE
                 → Source.Entity
                 → Env.EE
                 → Prop where
  | VAR_ENT :
    x ∈ Env.dom ve →
    ee' = ⟨[], ⟨[],[]⟩, ⟨[],Env.restrict de₂ [x]⟩, Env.restrict ve [x]⟩ →
    -------------------------------------------------------------
    《entity》⟨ce, te, ⟨de₁,de₂⟩, ve⟩ ⊢ Source.Entity.var x ፥ ee' ▪

  | TYPE_SOME :
    ⟨T, Env.TE_Item.DataType χ⟩ ∈ te₁ →
    xs ⊆ Env.fields de₂ χ →
    Ks ⊆ Env.constrs de₁ χ →
    ee' = ⟨[], ⟨Env.restrict te [T],[]⟩, ⟨Env.restrict de₁ Ks, Env.restrict de₂ xs⟩, Env.restrict ve xs⟩ →
    ------------------------------------------------------------------------------
    《entity》⟨ce, ⟨te₁,te₂⟩, ⟨de₁,de₂⟩, ve⟩ ⊢ Source.Entity.type_some T xs Ks ፥ ee' ▪

  | TYPE_ALL :
    ⟨T, Env.TE_Item.DataType χ⟩ ∈ te₁ →
    xs = Env.fields de₂ χ →
    Ks = Env.constrs de₁ χ →
    ee' = ⟨[], ⟨Env.restrict te [T],[]⟩, ⟨Env.restrict de₁ Ks,Env.restrict de₂ xs⟩, Env.restrict ve xs⟩ →
    -------------------------------------------------------------------------
    《entity》⟨ce, ⟨te₁,te₂⟩, ⟨de₁,de₂⟩, ve⟩ ⊢ Source.Entity.type_all T  ፥ ee' ▪


  | TYPE_SYN :
    ⟨T, Env.TE_Item.TypeSynonym χ h αs τ⟩ ∈ te₁ →
    ee' = ⟨[], ⟨Env.restrict te₁ [T],[]⟩, ⟨[], []⟩, []⟩ →
    ------------------------------------------------------------------------
    《entity》⟨ce, ⟨te₁,te₂⟩, de, ve⟩ ⊢ Source.Entity.type_some T [] [] ፥ ee' ▪


  | CLASS_SOME :
    ⟨C, Env.CEEntry.mk Γ h x_def α ie_sup⟩ ∈ ce →
    xs ⊆ Env.ops ve Γ →
    ee' = ⟨Env.restrict ce [C], ⟨[], []⟩, ⟨[], []⟩, Env.restrict ve xs⟩ →
    --------------------------------------------------------------------
    《entity》⟨ce, te, de, ve⟩ ⊢ Source.Entity.class_some C xs ፥ ee' ▪

  | CLASS_ALL :
    ⟨C, Env.CEEntry.mk Γ h x_def α ie_sup⟩ ∈ ce →
    xs = Env.ops ve Γ →
    ee' = ⟨Env.restrict ce [C], ⟨[], []⟩, ⟨[], []⟩, Env.restrict ve xs⟩ →
    --------------------------------------------------------------------
    《entity》⟨ce, te, de, ve⟩ ⊢ Source.Entity.class_all C ፥ ee' ▪

/--
Cp. Fig 12
```text
FE, SE ⊢ ent : FE
```
-/
inductive Export : Env.FE
                 → Env.SE
                 → Source.Entity
                 → Env.FE
                 → Prop where
  | EXPORT_MODULE :
    cs = Env.class_names_for_module se m →
    ts = Env.type_names_for_module se m →
    xs = _ → -- xs = {x | x : M ∈ VS} ∪ {x | x : M ∈ DS} →
    -- Ks = {K | K : M ∈ KS} →
    fe = Env.FE.mk (Env.restrict ce _) ⟨(Env.restrict te₁ _),_⟩ _ ie (Env.restrict ve xs) →
    -----------------------------------------------------------------------
    《export》⟨ce, ⟨te₁,te₂⟩, de, ie, ve⟩ , se ⊢ Source.Entity.module m ፥ fe ▪

  | EXPORT_ENTITY :
    《entity》⟨ce, te, de, ve⟩ ⊢ ent ፥ ⟨ce', te', de', ve'⟩ ▪ →
    ---------------------------------------------
    《export》⟨ce, te, de, ie, ve⟩ ,se ⊢ ent ፥ _ ▪


/--
Cp. Fig 13
```text
M, EE ⊢ implist, EE
```
-/
inductive Implist : Module_Name
                  → Env.EE
                  → Source.ImportList
                  → Env.EE
                  → Prop where
  | LIST_SOME :
    Forall2 ents ees (λ ent eeᵢ => 《entity》ee ⊢ ent ፥ eeᵢ ▪) →
    ee' = Env.ee_unions ees →
    -----------------------------------------------------------------------------------------------------------------
    《implist》M, ee ⊢ Source.ImportList.list_some ents ፥ Env.OplusTilde.oplustilde ee' (Env.Qualify.qualify m ee') ▪

  | HIDE_SOME :
    Forall2 ents ees (λ ent eeᵢ => 《entity》ee ⊢ ent ፥ eeᵢ ▪) →
    ⟨ce, te, de, ve⟩ = ee /- ee \ ees -/ →
    Ks = Source.constrs ents →
    ee' = ⟨ce, te, _ /- de \ Ks -/, ve ⟩ →
    ----------------------------------------------------------------------------------------------------------------
    《implist》M, ee ⊢ Source.ImportList.hide_some ents ፥ Env.OplusTilde.oplustilde ee' (Env.Qualify.qualify m ee') ▪

  | ALL :
    -----------------------------------------------------------------------------------------------------
    《implist》M, ee ⊢ Source.ImportList.empty ፥ Env.OplusTilde.oplustilde ee (Env.Qualify.qualify m ee) ▪

/--
Cp. Fig 13
```text
EE ⊢ qualifier, EE
```
-/
inductive Qualifier : Env.EE
                    → Source.Qualifier
                    → Env.EE
                    → Prop where
  | QUALIFIED :
    ---------------------------------------------------------------------
    《qualifier》ee ⊢ Source.Qualifier.qualified ፥ Env.JustQs.justQs ee ▪

  | UNQUALIFIED :
    -----------------------------------------------------
    《qualifier》ee ⊢ Source.Qualifier.unqualified ፥ ee ▪

/--
Cp. Fig 13
```text
ME ⊢ imp, FE, SE
```
-/
inductive Import : Env.ME
                 → Source.Import
                 → Env.FE
                 → Env.SE
                 → Prop where
  | IMPORT :
    ⟨M, ⟨ce, te, de, ie,ve⟩⟩ ∈ me →
    《implist》M', ⟨ ce, te, de, ve ⟩ ⊢ implist ፥ ee ▪ →
    《qualifier》ee ⊢ qualifier ፥ ⟨ce', te', de', ve'⟩ ▪ →
    -- SE = ⟨ dome(CE'), dom(TE'), dom(DE'), dom(VE') ⟩ : M →
    --------------------------------------------------------------------------------------
    《import》me ⊢ Source.Import.mk qualifier M M' implist ፥ ⟨ce', te', de', ie, ve'⟩, se ▪
