import Std
import Common.DDClasses

structure BDD where
  tree : Node
  unusedId : Nat := 2
deriving BEq

def BDD.addNewConstant (self: BDD) (_value : Bool) : BDD :=
  self

def BDD.addNewVar (self: BDD) (_index : Nat) (_low _high : Node) : BDD :=
  self

instance : DecisionDiagram BDD where
  allNodes (self : BDD) := Node.toHashSet self.tree
  addNewConstant := BDD.addNewConstant
  addNewVar (self : BDD) (index : Nat) (low high : Node) := self.addNewVar index low high
--  buildIndexer : BDD → Std.HashMap BDD Nat × Std.HashMap Nat BDD := sorry

example : (default : Node).index = 0 := rfl
