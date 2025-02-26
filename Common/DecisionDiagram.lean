import Std.Data.HashSet
import Common.Node

open Std

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams.
-/
class DecisionDiagram (α : Type) [BEq α] where
  --  numberOfPaths : α → Nat
  allNodes : α → HashSet Node
  addNewConstant : α → Bool → Node × α
  addNewVar (self : α) (varId : Nat) (low high : Node) : Node × α

class ReducibleDecisionDiagram (α : Type) [BEq α] extends DecisionDiagram α where
  reduce : α → α
  apply : α → (Bool → Bool → Bool) → Bool → α
  compose : α → α → α
