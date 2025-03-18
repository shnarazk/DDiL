import Common.GraphShape
import Common.DecisionDiagram
import Graph.Def

open Std

structure ZDD extends Graph

instance : Inhabited ZDD := ⟨{toGraph := default}⟩

instance : ToString ZDD where
  toString bdd := s!"[bdd {bdd.toGraph}]"

instance : BEq ZDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe ZDD Graph where
  coe b := b.toGraph

instance : Coe ZDD (Array Node) where
  coe b := b.toGraph.nodes

def ZDD.addNode (self: ZDD) (node : Node) : ZDD × Nat :=
  self.toGraph.addNode node
    |> fun (g, n) => ({self with toGraph := g}, n)

def ZDD.addNode' (self: ZDD) (varId : Nat) (li hi : Ref) : ZDD × Nat :=
  self.addNode {varId, li, hi}

namespace ZDD

variable (g : Graph)

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
      let (counter, a) := countPaths g counter node.li
      let (counter, b) := countPaths g counter node.hi
      (counter.insert r (a + b), (a + b))

-- private def order_to_scan (ia ib : Nat) : Bool := g.nodes[ia]! < g.nodes[ib]!

end ZDD

def ZDD.numSatisfies (self : ZDD) : Nat :=
  if self.nodes.isEmpty then
    1
  else
    ZDD.countPaths self.toGraph Std.HashMap.empty (Ref.to self.toGraph.nodes.size.pred) |>.snd
