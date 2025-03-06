import Std.Data.HashSet
import Common.Node
import Common.GraphShape

open Std
-- class NodeOf (γ : Type) [GraphShape γ] where

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  -- numberOfPaths : α → Nat
  allNodes : α → HashSet (Node γ)
  addNewConstant : α → Bool → (Node γ) × α
  addNewNode (self : α) (varId low high : Nat) : Nat × α

class ReducibleDecisionDiagram (α : Type) [BEq α] extends DecisionDiagram α where
  /-- Normalize to a valid representation -/
  reduce : α → α
  apply : α → (Bool → Bool → Bool) → Bool → α
  /-- Combine two diagrams into one -/
  compose : α → α → α
