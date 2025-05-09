import Common.GraphShape
import Common.DecisionDiagram
import Graph.Basic

open Std

structure ZDD extends Graph

instance : Inhabited ZDD := ⟨{toGraph := default}⟩

instance : ToString ZDD where toString zdd := s!"[zdd {zdd.toGraph}]"

instance : BEq ZDD where beq a b := a.toGraph == b.toGraph

instance : Coe ZDD Graph where coe b := b.toGraph

instance : Coe ZDD (Array Node) where coe b := b.toGraph.nodes

def ZDD.addNode (z: ZDD) (node : Node) : ZDD := {z with toGraph := z.toGraph.addNode node}

def ZDD.addNode' (z: ZDD) (varId : Nat) (li hi : Ref) : ZDD := z.addNode {varId, li, hi}

namespace ZDD_count

abbrev Counter := HashMap Ref Nat

private partial
def countPaths (g : Graph) (r : Ref) (counter : Counter := HashMap.emptyWithCapacity)
    : Counter × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then
      (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a) := countPaths g node.li counter
      let (counter, b) := countPaths g node.hi counter
      (counter.insert r (a + b), (a + b))

end ZDD_count

def ZDD.numSatisfies (z : ZDD) : Nat :=
  if z.nodes.isEmpty then 1 else ZDD_count.countPaths z.toGraph (Ref.last z.toGraph.nodes) |>.snd
