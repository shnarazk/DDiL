import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Common.LiftedBool
import Graph.Basic
import BDD.Reduce

open Std LiftedBool

namespace BDD_apply

abbrev Key := HashMap (Ref × Ref) Ref

partial def apply_aux (f : BinaryFunction) (r₁ r₂ : Ref) (nodes : Array Node) (merged : Key)
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
      let varId : Nat := Nat.min node1.varId node2.varId
      let (l1, h1) := if varId == node1.varId then (node1.li, node1.hi) else (r₁, r₁)
      let (l2, h2) := if varId == node2.varId then (node2.li, node2.hi) else (r₂, r₂)
      let (li, nodes, merged) := apply_aux f l1 l2 nodes merged
      let (hi, nodes, merged) := apply_aux f h1 h2 nodes merged
      let r := Ref.to nodes.size
      (r, nodes.push {varId, li, hi}, merged.insert (r₁, r₂) r)

end BDD_apply

def BDD.apply (operator : BinaryFunction) (self other : BDD) : BDD :=
  let all_nodes : Array Node := Node.append_nodes ↑self ↑other
  let r1 := Ref.to self.toGraph.nodes.size.pred
  let r2 := Ref.to all_nodes.size.pred
  BDD_apply.apply_aux operator r1 r2 all_nodes HashMap.emptyWithCapacity
    |> (fun (_, (nodes : Array Node), _) ↦ if nodes.isEmpty
        then default
        else Graph.fromNodes (Nat.max self.numVars other.numVars) nodes )
    |> (·.compact.toBDD)
