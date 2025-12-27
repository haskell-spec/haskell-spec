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
  | as : Names.QVariable → Pattern → Pattern
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
