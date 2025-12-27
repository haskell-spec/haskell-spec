import HaskellSpec.Names
namespace Source


/--
Distinguishes between qualified and unqualified imports.
```text
qualifer ∈ Qualifier → qualified
                     | ε
```
-/
inductive Qualifier : Type where
  | qualified
  | unqualified

/--
An entity is something that can be exported or imported by a module.
```text
ent ∈ Entity → x
             | K
             | T (x₁,...,xₖ;K₁,...,Kₙ)   k, n ≥ 0
             | T (..)
             | C (x₁,...,xₖ)             k    ≥ 0
             | C (..)
             | module M
```
-/
inductive Entity : Type where
  | var        : Names.QVariable → Entity
  | cons       : Names.QConstructor → Entity
  | type_some  : Names.QType_Name → List Names.QVariable → List Names.QConstructor → Entity
  | type_all   : Names.QType_Name → Entity
  | class_some : Names.QClassName → List Names.QVariable → Entity
  | class_all  : Names.QClassName → Entity
  | module     : Names.Module_Name → Entity -- use QModule_Name

def constrs (ents : List Entity) : List Names.QConstructor :=
  let pred ent := match ent with
    | Entity.cons K => some K
    | _ => none
  ents.filterMap pred

/--
```text
implist ∈ Import list → [[hiding] (ent₁,...,entₙ)]
                        n ≥ 0
```
-/
inductive ImportList : Type where
  | hide_some  : List Entity → ImportList
  | list_some : List Entity → ImportList
  | empty

/--
```text
imp ∈ Import → import qualifier M as M' implist
```
-/
structure Import : Type where
  qualified : Qualifier
  from_mod : Names.Module_Name
  as_mod : Names.Module_Name
  entities : ImportList

end Source
