import Std
import Common.DDClasses

inductive BDD where
  | leaf (id' : Nat) (value : Bool)
  | node (id' : Nat) (left right : BDD)
deriving BEq, Hashable, Repr

instance : Inhabited BDD where
  default := .leaf 0 false

def BDD.id (self : BDD) : Nat := match self with
  | .leaf id' _ => id'
  | .node id' _ _ => id'

def BDD.low (self : BDD) : Option BDD := match self with
  | .leaf _ _ => none
  | .node _ left _ => some left

def BDD.high (self : BDD) : Option BDD := match self with
  | .leaf _ _ => none
  | .node _ _ right => some right

instance : DecisionDiagramTree BDD where
  id := BDD.id
--  newConstant : Bool → BDD := sorry
--  addNewVar (index: Nat) (low high : BDD) : BDD := sorry
--  isConstant : BDD → Bool := sorry
--  unifiedKey : BDD → Nat := sorry
--  index : BDD → Option Nat := sorry
  low := BDD.low
  high := BDD.high
--  buildIndexer : BDD → Std.HashMap BDD Nat × Std.HashMap Nat BDD := sorry

example : (default : BDD).id = 0 := rfl

instance : ToString BDD where
  toString := fun bdd => match bdd with
    | .leaf id' value => s!"leaf {id'} {value}"
    | .node id' left right => s!"node {id'} {left.id} {right.id}"
