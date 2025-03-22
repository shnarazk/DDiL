import Common.Combinators
import Common.GraphShape
import Common.LiftedBool

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  numberOfSatisfyingPaths : α → Nat
  apply : LiftedBool.BinaryFunction → α → α → α
  /-- Combine two diagrams into one as follows
  f1 \ xi=f2
  So this a sort of substitution. -/
  compose : α → α → Nat → α
  /--
  Check if two diagrams are congruent.
  Two diagrams are congruent if they have the same satisfying paths. -/
  isCongruent : α → α → Bool
  /--
  Return true if the bool expression satisfies the graph. -/
  contains: α → List Int → Bool
