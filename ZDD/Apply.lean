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
    |> (fun (g : Graph) ↦ g.toZDD₂)

/-
-- ZDDと列挙問題 -- 最新の技法とプログラミングツール
Algorithm 1: Getnode(x, F₀, F₁)
  if F₁ is true then
    (F₀, table)
  else if let some F := table.get {varId := x, li := F₀, hi := F₁} then
    (F, table)
  else
    let F := [varId := x, li := F₀, hi := F₁}
    (F, table.insert F)

Algorithm 5: Apply(⋄, F, G)
  if F or G is terminal then
    return (F ⋄ G) as ZDD
  if F.index == G.index then
    let x  := F.index -- varId
    let H₀ := Apply(⋄, F.child[0], G.child[0])
    let H₁ := Apply(⋄, F.child[1], G.child[1])
  else if F.index < G.index then
    let x  := F.index
    let H₀ := Apply(⋄, F.child[0], G)
    let H₁ := Apply(⋄, F.child[1], G)
  else
    let x  := G.index
    let H₀ := Apply(⋄, F, G.child[0])
    let H₁ := Apply(⋄, F, G.child[1])
  Getnode(x, H₀, H₁)

-/
