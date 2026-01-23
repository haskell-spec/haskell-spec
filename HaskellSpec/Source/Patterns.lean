import HaskellSpec.Names
import HaskellSpec.Source.Literals

namespace Source

/--
### Patterns
**Note:** `n+k`-patterns are part of Haskell 98 but have been removed from the formalization.
-/
inductive Pattern : Type where
    /--
    A variable pattern.

    Faxen adds the following note at the beginning of section 9:

    "For the benefit of method bindings in instance declarations, the abstract
     syntax of patterns and the PVAR rule allow single variables to be qualified.
     The translated pattern is still unqualified but the returned environment
     associates the type with the qualified name since it is checked against the
     (possibly imported) variable in the INST rule [..]. Variables also occur in
     as-patterns `v@p` [..] where only unqualified variables are allowed."
    -/
  | var : Names.QVariable → Pattern
    /--
    A constructor pattern.
    Example: `Student name id`
    -/
  | constructor : Names.QConstructor → List Pattern → Pattern
    /--
    A labelled constructor pattern.
    Example: `Student { name = name, id = id }`
    -/
  | constructor_labelled : Names.QConstructor → List (Names.Variable × Pattern) → Pattern
    /--
    An as-pattern.
    Example: `s @ Student name id`
    -/
  | as : Names.Variable → Pattern → Pattern
    /--
    A lazy pattern.
    Example: `~p`
    -/
  | lazy : Pattern → Pattern
    /--
    A wildcard pattern.
    Example: `_`
    -/
  | wildcard : Pattern
    /--
    A literal pattern.
    Examples: `5`, `"hello world"`, `'c'`
    -/
  | literal : Literal → Pattern

end Source
