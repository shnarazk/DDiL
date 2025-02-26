import Std
import Common.Node
import Common.DecisionDiagram

open Std

structure BDD where
  tree : Node
  nodes : HashMap Nat Node := HashMap.empty |>.insert 0 Node.isFalse |>.insert 1 Node.isTrue
  has_false : 0 ∈ nodes := by trivial
  has_true : 1 ∈ nodes := by trivial
  unusedId : Nat := 2

instance : BEq BDD where
  beq (self other : BDD) := Node.is_congruent self.tree other.tree

def BDD.mkConstant (self: BDD) (value : Bool) : Node × BDD :=
  (if value then self.nodes[1]'self.has_true else self.nodes[0]'self.has_false, self)

def BDD.mkNewVar (self: BDD) (varId : Nat) (low high : Node) : Node × BDD :=
  (Node.newVar varId low high self.unusedId, {self with unusedId := self.unusedId + 1})

instance : DecisionDiagram BDD where
  allNodes (self : BDD) := self.nodes |>.values |> HashSet.ofList
  addNewConstant := BDD.mkConstant
  addNewVar := BDD.mkNewVar

example : (default : Node).toVarId = 0 := rfl
