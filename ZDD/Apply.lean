import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Common.LiftedBool
import Graph.Basic
import Graph.Node
import ZDD.Reduce
import ZDD.Conversion

open Std

namespace ZDD_apply

variable (g : Graph)

abbrev Key := HashMap (Ref × Ref) Ref

private partial def apply (f : LiftedBool.BinaryFunction) (r₁ r₂ : Ref) (nodes : Array Node) (merged : Key)
    : (Ref × (Array Node) × Key) :=
  if let some r := merged.get? (r₁, r₂) then
    (r, nodes, merged)
  else if let some b := f.apply r₁.asBool r₂.asBool then
    let r := Ref.bool b
    (r, nodes, merged.insert (r₁, r₂) r)
  else match r₁.link, r₂.link with
    | none,   none   =>
        let r := Ref.bool <| (↑f : Bool → Bool → Bool) r₁.grounded r₂.grounded
        (r, nodes, merged.insert (r₁, r₂) r)
    | none,   some _ => (r₂, nodes, merged.insert (r₁, r₂) r₂)
    | some _, none   => (r₁, nodes, merged.insert (r₁, r₂) r₁)
    | some a, some b =>
      let node1 : Node := nodes[a]!
      let node2 : Node := nodes[b]!
      let vi : Nat := Nat.min node1.varId node2.varId
      let (l1, h1) := if vi == node1.varId then (node1.li, node1.hi) else (r₁, r₁)
      let (l2, h2) := if vi == node2.varId then (node2.li, node2.hi) else (r₂, r₂)
      let (l, nodes, merged) := apply f l1 l2 nodes merged
      let (h, nodes, merged) := apply f h1 h2 nodes merged
      let r := Ref.to nodes.size
      (r, nodes.push {varId := vi, li := l, hi := h}, merged.insert (r₁, r₂) r)

end ZDD_apply

def ZDD.apply (operator : LiftedBool.BinaryFunction) (self other : ZDD) : ZDD :=
  let r1 := Ref.to self.toGraph.nodes.size.pred
  let all_nodes : Array Node := Node.append_nodes ↑self ↑other
  let r2 := Ref.to all_nodes.size.pred
  ZDD_apply.apply operator r1 r2 all_nodes HashMap.empty
    |> (fun (_, (nodes : Array Node), _) ↦ if nodes.isEmpty
        then (default : Graph)
        else Graph.fromNodes (Nat.max self.numVars other.numVars) nodes /- (Node.compact nodes)-/ )
    |>(fun g ↦ g.toZDD₂)
