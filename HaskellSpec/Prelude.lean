import HaskellSpec.Names
import HaskellSpec.SemanticTypes

/-!
# Prelude
-/
namespace Prelude

/-
## Module Names
-/

def hs_prelude : Names.Module_Name := Names.Module_Name.Mk "Prelude"

def hs_ratio : Names.Module_Name := Names.Module_Name.Mk "Ratio"

/-
## Haskell Types in the Prelude
-/


/--
The type `Prelude!Char`
-/
def char : SemTy.TypeS :=
  SemTy.TypeS.TypeConstructor (SemTy.Type_Constructor.Mk (Names.OType_Name.Qualified hs_prelude (Names.Type_Name.Mk "Char")) SemTy.Kind.Star)

/--
The type `Prelude!Bool`
-/
def bool : SemTy.TypeS :=
  SemTy.TypeS.TypeConstructor (SemTy.Type_Constructor.Mk (Names.OType_Name.Qualified hs_prelude (Names.Type_Name.Mk "Bool")) SemTy.Kind.Star)

/--
The type `[] : * → *`
-/
def list : SemTy.TypeS :=
  SemTy.TypeS.TypeConstructor (SemTy.Type_Constructor.Mk (Names.OType_Name.Special Names.Special_Type_Constructor.List) (SemTy.Kind.Fun SemTy.Kind.Star SemTy.Kind.Star))

def mk_list (α: SemTy.TypeS): SemTy.TypeS :=
 SemTy.TypeS.App list α

/--
The type `-> : * → * → *`
-/
def funt : SemTy.TypeS :=
  SemTy.TypeS.TypeConstructor (SemTy.Type_Constructor.Mk (Names.OType_Name.Special Names.Special_Type_Constructor.Fun) (SemTy.Kind.Fun SemTy.Kind.Star (SemTy.Kind.Fun SemTy.Kind.Star SemTy.Kind.Star)))

def mk_funt (α β : SemTy.TypeS) : SemTy.TypeS :=
  SemTy.TypeS.App (SemTy.TypeS.App funt α) β

/-
## Names of Type Classes
-/

def eq : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Eq")) SemTy.Kind.Star

def ord : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Ord")) SemTy.Kind.Star

def num : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Num")) SemTy.Kind.Star

def integral : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Integral")) SemTy.Kind.Star

def fractional : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Fractional")) SemTy.Kind.Star

def enum : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Enum")) SemTy.Kind.Star

def monad : SemTy.SClass_Name :=
  SemTy.SClass_Name.mk (Names.OClass_Name.Qualified hs_prelude (Names.Class_Name.mk
  "Monad")) (SemTy.Kind.Fun SemTy.Kind.Star SemTy.Kind.Star)

/-
## Names of Type Class Methods
-/

def enum_from : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "enumFrom")

def enum_from_then : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "enumFromThen")

def enum_from_to : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "enumFromTo")

def enum_from_then_to : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "enumFromThenTo")

def frominteger : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "fromInteger")

def fromrational : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "fromRational")

def equals : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "(==)")

def bind : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "(>>=)")

def sequence : Names.QVariable :=
  Names.QVariable.Qualified hs_prelude (Names.Variable.Mk "(>>)")

/-
## Names of Constructors
-/

def ratio_percent : Names.QVariable :=
  Names.QVariable.Qualified hs_ratio (Names.Variable.Mk "(%)")

end Prelude
