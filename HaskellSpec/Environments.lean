import HaskellSpec.Names
import HaskellSpec.SemanticTypes

namespace Env

/-
# Environments

Environments are represented as association lists, i.e. lists of tuples of key and value.
The various operations on environments are described in section 2.7 of the paper.
-/

@[reducible]
def Env (name info : Type) : Type :=
  List (name × info)


/-- Domain of an environment -/
def dom (env : Env name info) : List name :=
  List.map Prod.fst env

/-- Range of an environment -/
def rng (env : Env name info) : List info :=
  List.map Prod.snd env

/-- This is written `E / names` in the paper. -/
def remove [BEq name] (env : Env name info) (names : List name) : Env name info :=
  List.filter (Bool.not ∘ (List.contains names) ∘ Prod.fst) env

/-- This is written `E | names` in the paper. -/
def restrict [BEq name] (env : Env name info) (names : List name) : Env name info :=
  List.filter (List.contains names ∘ Prod.fst) env


def intersect [BEq t] (l l' : List t) : (List t) :=
  List.filter (List.contains l') l

class OPlus (m : Type) where
  oplus :  m -> m -> m -> Prop
  oplus_many : List m -> m -> Prop

notation  "《oplus》" e₁ "⊞" e₂ "≡" e₃ "▪"=> OPlus.oplus e₁ e₂ e₃
notation  "《oplus*》⊞{" es "}≡" e "▪"=> OPlus.oplus_many es e

-- ⊕ from Section 2.7 as a ternary relation
-- asserts that the environments have no overlapping domains
inductive oplus_env : Env k v -> Env k v -> Env k v -> Prop where

  | Nil :
    ------------
    oplus_env [] E E

  | Cons :
    k ∉ dom E₂ →
    oplus_env E₁ E₂ E₃ →
    -------------------------------------
    oplus_env ((k, v) :: E₁) E₂ ((k, v) :: E₃)

inductive oplus_many_env : List (Env k v) → Env k v → Prop where
  | Nil :
    ----------------
    oplus_many_env [] []

  | Cons :
    oplus_many_env es e' →
    oplus_env e e' e'' →
    ------------------------
    oplus_many_env (e :: es) e''


instance oplus_env_inst : OPlus (Env k v) where
  oplus := oplus_env
  oplus_many := oplus_many_env


def oplusbar [BEq name] (env env' : Env name info) (_ : (restrict env (dom env') = restrict env' (dom env))) : (Env name info) :=
  List.append env env'

def oplusarrow [BEq name] [BEq info] (env env' : Env name info) : (Env name info) :=
  List.append (remove env (dom env')) env'

/-- This operation is written `⊕^~` in the paper.-/
class OplusTilde (env : Type) where
  oplustilde (env₁ env₂ : env) : env

instance instOplusTildeEnv : OplusTilde (Env name info) where
  oplustilde env₁ env₂ := List.append env₁ env₂

class Qualify (env : Type) where
  qualify  (m : Names.Module_Name) (e : env) : env

instance instQualifyEnv [Qualify name] : Qualify (Env name info) where
  qualify m env := env.map (λ ⟨name, info⟩ => ⟨Qualify.qualify m name, info⟩)

instance instQualifyQClassName : Qualify Names.QClassName where
  qualify m name := match name with
    | Names.QClassName.Qualified _ c => Names.QClassName.Qualified m c
    | Names.QClassName.Unqualified c => Names.QClassName.Qualified m c

instance instQualifyQType_Name : Qualify Names.QType_Name where
  qualify m name := match name with
    | Names.QType_Name.Qualified _ t => Names.QType_Name.Qualified m t
    | Names.QType_Name.Unqualified t => Names.QType_Name.Qualified m t
    | Names.QType_Name.Special s => Names.QType_Name.Special s

instance instQualifyQConstructor : Qualify Names.QConstructor where
  qualify m name := match name with
    | Names.QConstructor.Qualified _ c => Names.QConstructor.Qualified m c
    | Names.QConstructor.Unqualified c => Names.QConstructor.Qualified m c
    | Names.QConstructor.Special s => Names.QConstructor.Special s

instance instQualifyQVariable : Qualify Names.QVariable where
  qualify m var := match var with
    | Names.QVariable.Qualified _ v => Names.QVariable.Qualified m v
    | Names.QVariable.Unqualified v => Names.QVariable.Qualified m v

def unQual [Names.Unqual name] : Env name info -> Env name info :=
  List.map (λ(n, i) => (Names.Unqual.unQual n, i))

class JustQs (env : Type) where
  justQs : env -> env

instance instJustQsEnv [Names.IsQual name] : JustQs (Env name info) where
  justQs := List.filter (Names.IsQual.isQual ∘ Prod.fst)


/--
This function is defined at the beginning of section 2.7.
It retains only information about names with a single entry.
-/
def justSingle [BEq name] [BEq info] (env : Env name info) : Env name info :=
  env.filter (λ ⟨name,_⟩ => (env.filter (λ ⟨name',_⟩ => name == name')).length == 1)

#guard justSingle [("a", ()), ("a", ())] == []
#guard justSingle [("a", ()), ("b", ())] == [("a", ()),("b", ())]
#guard justSingle [("a", ()), ("b", ()), ("b", ())] == [("a", ())]

inductive TE_Item : Type where
  | DataType : SemTy.Type_Constructor →  TE_Item
  | TypeSynonym : SemTy.Type_Constructor → Int → List SemTy.Type_Variable → SemTy.TypeS → TE_Item

instance instHasKindTE_Item : SemTy.HasKind TE_Item where
  get x := match x with
           | TE_Item.DataType c => SemTy.HasKind.get c
           | TE_Item.TypeSynonym c _ _ _ => SemTy.HasKind.get c

/-
### Type environment

The type environment contains information about type constructors and type variables.
The type constructor information is derived from type declarations in the program and
the type variable information records in-scope type variables.

Cp. section 2.7.2
-/

abbrev TE₁ : Type := Env Names.QType_Name TE_Item
abbrev TE₂ : Type := Env Names.Type_Variable SemTy.Type_Variable

structure TE : Type where
  te₁ : TE₁
  te₂ : TE₂

instance instJustQsTE : JustQs TE where
  justQs te :=
    { te₁ := JustQs.justQs te.te₁
      te₂ := te.te₂
    }

def TE_init : TE :=
  { te₁ := [(Names.QType_Name.Special Names.Special_Type_Constructor.List, TE_Item.DataType (SemTy.Type_Constructor.Mk (Names.OType_Name.Special Names.Special_Type_Constructor.List) (SemTy.Kind.Fun SemTy.Kind.Star SemTy.Kind.Star)))]
    te₂ := []
  }

def TE_union (te₁ te₂ : TE) : TE :=
  { te₁ := te₁.te₁ ++ te₂.te₁
    te₂ := te₁.te₂ ++ te₂.te₂
  }

def TE_empty : TE :=
  { te₁ := []
    te₂ := []
  }

instance oplus_te_inst : OPlus TE where
  oplus := λ te₁ te₂ te_output => OPlus.oplus te₁.te₁ te₂.te₁ te_output.te₁ ∧
                                  OPlus.oplus te₁.te₂ te₂.te₂ te_output.te₂
  oplus_many := λ te_in te_out => OPlus.oplus_many (List.map (λ x => x.te₁) te_in) te_out.te₁ ∧
                                  OPlus.oplus_many (List.map (λ x => x.te₂) te_in) te_out.te₂

instance instQualifyTE₂ : Qualify TE₂ where
  qualify _ env := env -- Type variables cannot be qualified.

instance instQualifyTE : Qualify TE where
  qualify m te :=
    { te₁ := Qualify.qualify m te.te₁
      te₂ := Qualify.qualify m te.te₂
    }

/-
## Instance Environment
-/

/--
Section 2.7.4

The definition of IE_Entry is implicit in the definition of IE.

Note: We are using the type Variable from the source language for x,
instead of a separate type for the semantic syntax. For v, we use
QVariable instead of a type for the semantic syntax.
-/
inductive IE_Entry : Type where
/--
v is bound in a dictionary abstraction
```text
v : Γ (α τ_1 … τ_k)
```
-/
  | BoundInDictionaryAbstraction : Names.Variable
    -> SemTy.SClass_Name -> SemTy.Type_Variable
    -> List SemTy.TypeS -> IE_Entry
/--
x represents a superclass in classinfo
```text
x : Γ α
```
-/
  | SuperclassInClassinfo : Names.QVariable -> SemTy.SClass_Name
    -> SemTy.Type_Variable-> IE_Entry
/--
x is a dictionary from an instance declaration
```text
x : ∀α_1 … α_k . θ ⇒ Γ (χ α_1 … α_k)
```
-/
  | DictionaryFromInstanceDeclaration : Names.QVariable
    -> List SemTy.Type_Variable
    -> SemTy.Context
    -> SemTy.SClass_Name
    -> SemTy.Type_Constructor
    -> SemTy.Type_Variable-> IE_Entry
/--
x extracts a dictionary for the superclass Γ
```text
x : ∀α . Γ'α ⇒ Γα
```
-/
  | ExtractsADictionaryForTheSuperclass : Names.QVariable
    -> SemTy.Type_Variable
    -> SemTy.SClass_Name
    -> SemTy.SClass_Name
    -> IE_Entry

@[reducible]
def IE := List IE_Entry

/--
### Class environment

Cp. section 2.7.1
-/
structure CEEntry : Type where
  name : SemTy.SClass_Name
  h : Int
  var : Names.Variable
  class_name : Names.QClassName
  ie : IE

@[reducible]
def CE := Env Names.QClassName CEEntry

/--
Cp. Fig 16
-/
def CE_init : CE := []

/-
## Data Constructor Environment
-/

/-
### Update Environment
-/

abbrev UE : Type := Env Names.QVariable SemTy.TypeS

instance instSubstituteUE : SemTy.Substitute UE where
  substitute := sorry


/-
### Label Environment

Cp. section 2.7.3
-/

structure LabelInfo : Type where
  tyvars : List SemTy.Type_Variable
  context : SemTy.Context
  update_env : UE
  ty : SemTy.TypeS

abbrev LE : Type := Env Names.QConstructor LabelInfo

abbrev DE₁ : Type := Env Names.QConstructor (Names.QConstructor × SemTy.Type_Constructor × SemTy.TypeScheme)
abbrev DE₂ : Type := Env Names.QVariable (Names.QVariable × SemTy.Type_Constructor × LE)

def constrs (de : DE₁)(χ : SemTy.Type_Constructor) : List Names.QConstructor :=
  List.map Prod.fst (List.filter (λ ⟨_,info⟩ => info.snd.fst == χ) de)

def fields (de : DE₂)(χ : SemTy.Type_Constructor) : List Names.QVariable :=
  List.map Prod.fst (List.filter (λ ⟨_,info⟩ => info.snd.fst == χ) de)

/--
### Data constructor environment

Cp. section 2.7.3
-/
structure DE : Type where
  de₁ : DE₁
  de₂ : DE₂

instance instJustQsDE : JustQs DE where
  justQs de :=
    { de₁ := JustQs.justQs de.de₁
      de₂ := JustQs.justQs de.de₂
    }

instance instQualifyDE : Qualify DE where
  qualify m de :=
    { de₁ := Qualify.qualify m de.de₁
      de₂ := Qualify.qualify m de.de₂
    }


def DE_union (de₁ de₂ : DE) : DE :=
  { de₁ := de₁.de₁ ++ de₂.de₁
    de₂ := de₁.de₂ ++ de₂.de₂
  }

def DE_empty : DE :=
  { de₁ := []
    de₂ := []
  }

/--
### Overloading Environment

Cp. section 2.7.4
-/
inductive OE : Type where


inductive VE_Item : Type where
  | Ordinary : Names.QVariable → SemTy.TypeScheme → VE_Item
  | Class : Names.QVariable → SemTy.ClassTypeScheme → VE_Item
  deriving BEq


/--
### Variable Environment

Cp. section 2.7.5
-/
@[reducible]
def VE : Type :=
  Env Names.QVariable VE_Item

def ops (ve : VE)(Γ : SemTy.SClass_Name) : List Names.QVariable :=
  sorry

/-
### Kind Environment

The kind environment contains information about the kinds of class and type names and type variables.

Cp. section 2.7.6
-/

@[reducible]
def KE₁ : Type := Env Names.QType_Name SemTy.Kind

@[reducible]
def KE₂ : Type := Env Names.Type_Variable SemTy.Kind

@[reducible]
def KE₃ : Type := Env Names.QClassName SemTy.Kind

structure KE where
  ke₁ : KE₁
  ke₂ : KE₂
  ke₃ : KE₃


instance ke_oplus : OPlus KE where
  oplus ke₁ ke₂ ke₃ :=
    OPlus.oplus ke₁.ke₁ ke₂.ke₁ ke₃.ke₁ ∧
    OPlus.oplus ke₁.ke₂ ke₂.ke₂ ke₃.ke₂ ∧
    OPlus.oplus ke₁.ke₃ ke₂.ke₃ ke₃.ke₃
  oplus_many kes ke_out :=
    OPlus.oplus_many (List.map (λ x => x.ke₁) kes) ke_out.ke₁ ∧
    OPlus.oplus_many (List.map (λ x => x.ke₂) kes) ke_out.ke₂ ∧
    OPlus.oplus_many (List.map (λ x => x.ke₃) kes) ke_out.ke₃

/--
### Source Environment

Cp. section 2.7.7
-/
structure SE : Type where
  cs : List (Names.Class_Name × Names.Module_Name)
  ts : List (Names.QType_Name × Names.Module_Name)
  ds : List (Unit × Names.Module_Name)
  vs : List (Unit × Names.Module_Name)

def class_names_for_module (se: SE)(m : Names.Module_Name) : List Names.Class_Name :=
  let filtered := se.cs.filter (λ x => x.snd == m)
  filtered.map (λ x => x.fst)

def type_names_for_module (se: SE)(m : Names.Module_Name) : List Names.QType_Name :=
  let filtered := se.ts.filter (λ x => x.snd == m)
  filtered.map (λ x => x.fst)

/--
### Global Environment

Cp. section 2.7.8
-/
structure GE : Type where
  ce : CE
  te : TE
  de : DE

/--
### Full Environment

Cp. section 2.7.8
-/
structure FE : Type where
  ce : CE
  te : TE
  de : DE
  ie : IE
  ve : VE

def FE_union (fe₁ fe₂ : FE) : FE :=
  { ce := fe₁.ce ++ fe₂.ce
    te := TE_union fe₁.te fe₂.te
    de := DE_union fe₁.de fe₂.de
    ie := fe₁.ie ++ fe₂.ie
    ve := fe₁.ve ++ fe₂.ve
  }

def FE_empty : FE :=
  { ce := []
    te := TE_empty
    de := DE_empty
    ie := []
    ve := []
  }

/--
### Entity Environment

Cp. section 2.7.8
-/
structure EE : Type where
  ce : CE
  te : TE
  de : DE
  ve : VE

/-- An empty entity environment -/
def ee_empty : EE :=
  EE.mk [] ⟨[],[]⟩ ⟨[],[]⟩ []

instance instJustQsEE : JustQs EE where
  justQs ee :=
   { ce := JustQs.justQs ee.ce
     te := JustQs.justQs ee.te
     de := JustQs.justQs ee.de
     ve := JustQs.justQs ee.ve
   }

def ee_union (ee₁ ee₂ : EE) : EE :=
  { ce := ee₁.ce ++ ee₂.ce
    te := ⟨ee₁.te.te₁ ++ ee₂.te.te₁,ee₁.te.te₂ ++ ee₂.te.te₂⟩
    de := ⟨ee₁.de.de₁ ++ ee₂.de.de₁,ee₁.de.de₂ ++ ee₂.de.de₂⟩
    ve := ee₁.ve ++ ee₂.ve
  }


def ee_unions (ees : List EE) : EE :=
  ees.foldl ee_union ee_empty


instance instOplusTildeEE : OplusTilde EE where
  oplustilde ee₁ ee₂ :=
    { ce := OplusTilde.oplustilde ee₁.ce ee₂.ce
      te := ⟨ OplusTilde.oplustilde ee₁.te.te₁ ee₂.te.te₁
            , OplusTilde.oplustilde ee₁.te.te₂ ee₂.te.te₂ ⟩
      de := ⟨ OplusTilde.oplustilde ee₁.de.de₁ ee₂.de.de₁
            , OplusTilde.oplustilde ee₁.de.de₂ ee₂.de.de₂ ⟩
      ve := OplusTilde.oplustilde ee₁.ve ee₂.ve
    }

instance instQualifyEE : Qualify EE where
  qualify m ee :=
    { ce := Qualify.qualify m ee.ce
      te := Qualify.qualify m ee.te
      de := Qualify.qualify m ee.de
      ve := Qualify.qualify m ee.ve
    }

/--
### Module Environment

Cp. section 2.7.9
-/
@[reducible]
def ME : Type := Env Names.Module_Name FE


/-
### The kindsOf function
-/

def kindsOfCe (ce : CE) : KE₃ :=
  let f := λ ⟨C, ceentry⟩ => ⟨C, SemTy.HasKind.get ceentry.name⟩
  List.map f ce


def kindsOfTe₁ (te : TE₁) : KE₁ :=
  let f := λ ⟨q, te_item ⟩ => ⟨q, SemTy.HasKind.get te_item⟩
  List.map f te

def kindsOfTe₂ (te : TE₂) : KE₂ :=
  let f := λ ⟨u, ty_var⟩ => ⟨u, SemTy.HasKind.get ty_var⟩
  List.map f te

/--
The `kindsOf` function is described in section 2.7.6
-/
def kindsOf(ce : CE)(te: TE) : KE :=
  KE.mk (kindsOfTe₁ te.te₁) (kindsOfTe₂ te.te₂) (kindsOfCe ce)

end Env
