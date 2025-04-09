import Common.GraphShape
import Common.DecisionDiagram
import Graph.Basic

open Std

structure ZDD extends Graph

instance : Inhabited ZDD := ⟨{toGraph := default}⟩

instance : ToString ZDD where
  toString zdd := s!"[zdd {zdd.toGraph}]"

instance : BEq ZDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe ZDD Graph where
  coe b := b.toGraph

instance : Coe ZDD (Array Node) where
  coe b := b.toGraph.nodes

def ZDD.addNode (self: ZDD) (node : Node) : ZDD :=
  {self with toGraph := self.toGraph.addNode node}

def ZDD.addNode' (self: ZDD) (varId : Nat) (li hi : Ref) : ZDD :=
  self.addNode {varId, li, hi}

namespace ZDD

abbrev Counter := Std.HashMap Ref Nat

variable (g : Graph)

partial def countPaths (g : Graph) (counter : Counter) (r : Ref) : Counter × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then
      (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a) := countPaths g counter node.li
      let (counter, b) := countPaths g counter node.hi
      (counter.insert r (a + b), (a + b))

end ZDD

def ZDD.numSatisfies (self : ZDD) : Nat :=
  if self.nodes.isEmpty
  then 1
  else ZDD.countPaths self.toGraph Std.HashMap.emptyWithCapacity (Ref.last self.toGraph.nodes) |>.snd
