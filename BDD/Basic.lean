import Std
import Std.Data.HashMap
import Common.Node
import Common.DecisionDiagram

open Std
open Std.HashMap

structure BDD where
  tree : Node
  nodes : HashMap Nat Node := HashMap.empty |>.insert 0 Node.isFalse |>.insert 1 Node.isTrue
  has_false : nodes.contains 0 := by trivial
  has_true  : nodes.contains 1 := by trivial

instance : BEq BDD where
  beq (self other : BDD) := Node.is_congruent self.tree other.tree

def BDD.unusedId (self : BDD) : Nat := self.nodes.size

def BDD.mkConstant (self: BDD) (value : Bool) : Node × BDD :=
  (if value then self.nodes[1]'self.has_true else self.nodes[0]'self.has_false, self)

def BDD.mkNewVar (self: BDD) (varId : Nat) (low high : Node) : Node × BDD :=
  let k := self.unusedId
  let n := Node.newVar varId low high k
  let nodes := self.nodes
  let nodes₁ := nodes.insert k n
  (n, {self with
    nodes := nodes₁,
    has_false := by
      rw [contains_insert]
      exact Lean.Grind.Bool.or_eq_of_eq_true_right self.has_false
    has_true := by
      rw [contains_insert]
      exact Lean.Grind.Bool.or_eq_of_eq_true_right self.has_true
  })


instance : DecisionDiagram BDD where
  allNodes (self : BDD) := self.nodes |>.values |> HashSet.ofList
  addNewConstant := BDD.mkConstant
  addNewVar := BDD.mkNewVar

example : (default : Node).toVarId = 0 := rfl
