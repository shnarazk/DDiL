import Std.Data.HashMap

class DecisionDiagramTree (α : Type) [BEq α] [Hashable α] where
  id (self : α) : Nat
--  len : α → Nat
--  newConstant : Bool → α
--  addNewVar (index: Nat) (low high : α) : α
--  isConstant : α → Bool
--  unifiedKey : α → Nat
--  index : α → Option Nat
  low : α → Option α
  high : α → Option α
--  buildIndexer : α → Std.HashMap α Nat × Std.HashMap Nat α

class ReducibleDecisionDiagramTree (α : Type) [BEq α] [Hashable α] extends DecisionDiagramTree α where
  reduce : α → α
  apply : α → (Bool → Bool → Bool) → Bool → α
  compose : α → α → α

class DecisionDiagram (α : Type) where
  of (β : Type) [BEq β] [Hashable β] [DecisionDiagramTree β] : β → α
  unwrap (β : Type) [BEq β] [Hashable β] [DecisionDiagramTree β] : α → β
