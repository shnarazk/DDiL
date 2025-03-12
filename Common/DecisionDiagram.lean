import Common.GraphShape

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  numberOfSatisfyingPaths : α → Nat
  apply : (Bool → Bool → Bool) → Bool → α → α → α
  /-- Combine two diagrams into one -/
  compose : α → α → Nat → α
