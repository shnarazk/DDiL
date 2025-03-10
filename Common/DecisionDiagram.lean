import Std.Data.HashSet
import Common.Graph
import Common.GraphShape

open Std

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  numberOfPaths : α → Nat
  allNodes : α → HashSet (Nat × Node)

class ReducibleDecisionDiagram (α : Type) [BEq α] [GraphShape α] [DecisionDiagram α] where
  apply : α → (Bool → Bool → Bool) → Bool → α
  /-- Combine two diagrams into one -/
  compose : α → α → Nat → α
