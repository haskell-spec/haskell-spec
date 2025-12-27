import HaskellSpec.Names

/-!
# Semantic Types

Semantic types are defined in Fig. 4 of the paper.
-/
namespace SemTy

/--
```text
κ ∈ Kind → *
         | κ → κ
```
-/
inductive Kind : Type where
  | Star : Kind
  | Fun : Kind → Kind → Kind
  deriving BEq, Repr

def kind_fun_list (kes : List Kind) : Kind := sorry


export Kind (Star Fun)

class HasKind (α : Type) where
  get : α → Kind

/--
```text
Γ ∈ Class name → Cᵏ
```
-/
structure SClass_Name : Type where
  name : Names.OClass_Name
  kind : Kind
  deriving BEq, Repr

instance instHasKindSClass_Name : HasKind SClass_Name where
  get n := n.kind

/--
```text
χ ∈ Type constructor → Tᵏ
```
-/
inductive Type_Constructor : Type where
  | Mk : Names.OType_Name → Kind → Type_Constructor
  deriving BEq, Repr

instance instHasKindType_Constructor : HasKind Type_Constructor where
  get x := match x with
           | Type_Constructor.Mk _ kind => kind

/--
```text
α ∈ Type variable → uᵏ
```
-/
inductive Type_Variable : Type where
  | Mk : Names.Type_Variable → Kind → Type_Variable
  deriving BEq, Repr

instance instHasKindType_Variable : HasKind Type_Variable where
  get x := match x with
           | Type_Variable.Mk _ kind => kind

/--
```text
τ ∈ Type → α
         | χ
         | τ₁ τ₂
```
-/
inductive TypeS : Type where
  | Variable : Type_Variable → TypeS
  | TypeConstructor : Type_Constructor → TypeS
  | App : TypeS → TypeS → TypeS
  deriving BEq, Repr

/--
Builds the type `τ τ₁ … τₙ`
-/
def type_apps(τ : TypeS)(τs : List TypeS) : TypeS :=
  τs.foldl TypeS.App τ

/--
```text
θ ∈ Context → (Γ₁ τ₁, … , Γₙ τₙ)
```
-/

abbrev Context := List (SClass_Name × TypeS)

/--
```text
σ ∈ Type Scheme →  ∀ α₁ … αₖ.θ ⇒ τ
```
-/
inductive TypeScheme : Type where
  | Forall : List Type_Variable → Context → TypeS → TypeScheme
  deriving BEq, Repr

/--
This is written as follows in the paper:
```
∀ α. Γ α ⇒c σ
```
It is used to assign types to typeclass methods. The example given in the paper is:
```
ceiling : ∀ α. RealFrac α ⇒c ∀ β. Integral β ⇒ α → β
```
-/
inductive ClassTypeScheme : Type where
  | Forall : Type_Variable → SClass_Name → TypeScheme → ClassTypeScheme
  deriving BEq


/-
## Substitution of Types for Type Variables
-/

/--
A simultaneous substitution of types for type variables.
E.g.: `[τ₁ / α₁, … , τₙ / αₙ]`
-/
@[reducible]
def VarSubst : Type := List (SemTy.Type_Variable × SemTy.TypeS)

/--
A typeclass for types to which a type variable substitution can be applied.
-/
class Substitute (α : Type) where
  substitute : VarSubst → α → α

instance instSubstituteTypeS : Substitute TypeS where
  substitute subst τ :=
    let rec substitute_rec subst τ :=
      match τ with
      | TypeS.Variable α => Option.getD (List.lookup α subst) (SemTy.TypeS.Variable α)
      | TypeS.TypeConstructor χ => SemTy.TypeS.TypeConstructor χ
      | TypeS.App τ1 τ2 => SemTy.TypeS.App (substitute_rec subst τ1) (substitute_rec subst τ2);
    substitute_rec subst τ

instance instSubstituteContext : Substitute Context where
  substitute subst := List.map (Prod.map id (Substitute.substitute subst))

end SemTy
