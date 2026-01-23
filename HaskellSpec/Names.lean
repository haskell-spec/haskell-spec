/-!
# Names

There is a qualified and an unqualified variant for all names.
We call them X and QX, respectively.

Names are defined in Table 1 and Fig. 3 in the paper
-/

namespace Names

/--
### Module Name

Module names are written `M` in the paper. The Haskell 98 standard does
not have hierarchical modules, so this type does not have any structure.
-/
inductive Module_Name : Type where
  | Mk : String -> Module_Name
  deriving BEq, Repr

/--
### Variable

Unqualified variables are written `v` in the paper.
-/
inductive Variable : Type where
  | Mk : String → Variable
  deriving BEq, Repr

/--
### Original Variable

```text
x ∈ Original variable → v
                      | M!v
```
-/
inductive QVariable : Type where
  | Unqualified : Variable → QVariable
  | Qualified : Module_Name → Variable → QVariable
  deriving BEq, Repr

/--
### Special Data Constructor

```
Δ ∈ Special data constructor → ()
                             | (k)
                             | []
                             | (:)
```
-/
inductive Special_Data_Constructor where
  | Unit : Special_Data_Constructor
  | Tuple : Nat → Special_Data_Constructor
  | Nil : Special_Data_Constructor
  | Cons : Special_Data_Constructor
  deriving BEq, Repr


/--
### Constructor

Constructors are written as `J` in the paper.
-/
inductive Constructor : Type where
  | Mk : String → Constructor
  deriving BEq, Repr

/--
### Qualified Data Constructors

```text
K ∈ Qualified data constructor → J
                               | M.J
                               | Δ
```
-/
inductive QConstructor : Type where
  | Unqualified : Constructor → QConstructor
  | Qualified : Module_Name → Constructor → QConstructor
  | Special : Special_Data_Constructor → QConstructor
  deriving BEq, Repr

/--
### Special Type Constructor

```text
Σ ∈ Special type constructor → ()
                             | (k)
                             | []
                             | (->)
```
-/
inductive Special_Type_Constructor : Type where
  | Unit : Special_Type_Constructor
  | Tuple : Nat → Special_Type_Constructor
  | List : Special_Type_Constructor
  | Fun : Special_Type_Constructor
  deriving BEq, Repr

/--
```text
S ∈ Type constructor
```
-/
inductive Type_Name : Type where
  | Mk : String -> Type_Name
  deriving BEq, Repr

/--
### Qualified Type Name

```text
T ∈ Qualified type constructor → S
                               | M.S
                               | Σ
```
-/
inductive QType_Name : Type where
  | Unqualified : Type_Name → QType_Name
  | Qualified : Module_Name → Type_Name → QType_Name
  | Special : Special_Type_Constructor → QType_Name
  deriving BEq, Repr


/--
### Original Type Name

```text
T ∈ Original type name → S
                       | M!S
                       | Σ
```
-/
inductive OType_Name : Type where
  | Unqualified : Type_Name → OType_Name
  | Qualified : Module_Name → Type_Name → OType_Name
  | Special : Special_Type_Constructor → OType_Name
  deriving BEq, Repr

/--
### Type Variable

Type variables are written as `u` in the paper.
-/
inductive Type_Variable : Type where
  deriving BEq, Repr

/--
### Qualified Type Variable

Qualified type variables are written as `M` in the paper.
-/
inductive QType_Variable : Type where
  deriving Repr

/--
### Class Name

Class names are written as `B` in the paper.
-/
structure Class_Name : Type where
  name : String
  deriving BEq, Repr

/--
### Qualified Class Name

```text
C ∈ Qualified class name → B
                         | M.B
```
-/
inductive QClassName : Type where
  | Unqualified : Class_Name → QClassName
  | Qualified : Module_Name → Class_Name → QClassName
  deriving BEq, Repr


/--
### Original Type Name

```text
C ∈ Original class name → B
                        | M!B
```
-/
inductive OClass_Name : Type where
  | Unqualified : Class_Name → OClass_Name
  | Qualified : Module_Name → Class_Name → OClass_Name
  deriving BEq, Repr



/--
This class is informally specified at the end of section 2.3.
-/
class Unqual (name : Type u) where
  unQual : name -> name

instance instUnqualQClassName : Unqual QClassName where
  unQual
    | QClassName.Unqualified c => QClassName.Unqualified c
    | QClassName.Qualified _ c => QClassName.Unqualified c

instance instUnqualQConstructor : Unqual QConstructor where
  unQual
    | QConstructor.Unqualified c => QConstructor.Unqualified c
    | QConstructor.Qualified _ c => QConstructor.Unqualified c
    | QConstructor.Special s => QConstructor.Special s

def unqual_var (var : Names.QVariable) : Names.Variable :=
  match var with
    | (Names.QVariable.Qualified _m x) => x
    | (Names.QVariable.Unqualified x) => x

/--
This class needed for a polymorphic implementation of
the `justQs` function, defined in section 2.7.
-/
class IsQual (name : Type u) where
  isQual : name -> Bool

instance instIsqualQClassName : IsQual QClassName where
  isQual
    | QClassName.Unqualified _ => False
    | QClassName.Qualified _ _ => True

instance instIsqualQConstructor : IsQual QConstructor where
  isQual
    | QConstructor.Unqualified _ => False
    | QConstructor.Qualified _ _ => True
    | QConstructor.Special _ => False

instance instIsQualQTypeName : IsQual QType_Name where
  isQual
    | QType_Name.Unqualified _ => False
    | QType_Name.Qualified _ _=> True
    | QType_Name.Special _ => True -- TODO: Check if these count as qualified.

instance instIsQualQVariable : IsQual QVariable where
  isQual
    | QVariable.Qualified _ _ => True
    | QVariable.Unqualified _ => False

end Names
