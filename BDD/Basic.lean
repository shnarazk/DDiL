import Std.Data.HashMap
import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Graph.Basic

open Std

structure BDD extends Graph

instance : Inhabited BDD := ⟨{toGraph := default}⟩

instance : ToString BDD where
  toString bdd := s!"[bdd {bdd.toGraph}]"

instance : BEq BDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe BDD Graph where
  coe b := b.toGraph

instance : Coe BDD (Array Node) where
  coe b := b.toGraph.nodes

def BDD.addNode (self: BDD) (node : Node) : BDD × Nat :=
  self.toGraph.addNode node
    |> fun (g, n) => ({self with toGraph := g}, n)

def BDD.addNode' (self: BDD) (varId : Nat) (li hi : Ref) : BDD × Nat :=
  self.addNode {varId, li, hi}

namespace BDD

variable (g : Graph)

private def path_distance (a b : Ref) : Nat :=
  match a.link, b.link with
  | none,   none   => 0
  | none,   some _ => 0
  | some i, none   => 2 ^ (g.numVars - g.nodes[i]!.varId)
  | some i, some j => 2 ^ (g.nodes[j]!.varId - g.nodes[i]!.varId).pred

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
partial def countPaths (g : Graph) (counter : Std.HashMap Ref Nat) (r : Ref) : Std.HashMap Ref Nat × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a') := countPaths g counter node.li
      let a := (path_distance g r node.li) * a'
      let (counter, b') := countPaths g counter node.hi
      let b := (path_distance g r node.hi) * b'
      (counter.insert r (a + b), (a + b))

private def order_to_scan (ia ib : Nat) : Bool := g.nodes[ia]! < g.nodes[ib]!

end BDD

def BDD.numSatisfies (self : BDD) : Nat :=
  if self.nodes.isEmpty then
    2 ^ self.numVars
  else
    BDD.countPaths ↑self Std.HashMap.emptyWithCapacity (Ref.to self.toGraph.nodes.size.pred) |>.snd
