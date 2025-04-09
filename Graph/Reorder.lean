import Std.Data.HashMap
import Graph.Ref
import Graph.Basic

open Std

namespace Graph_reorder

abbrev HashMap := Std.HashMap

def includes (a b : Array Ref) : Bool :=
  b.all (a.contains ·)

partial
def topologicalSort (nodes : Array Node) (root : Ref) : HashMap Ref (Array Ref) :=
  nodes.zipIdx.foldl
    (fun m (node, i) ↦
      let r := Ref.to i
      let m := match node.li.link with
        | none   => m
        | some _ => m.alter node.li (if let some l := · then l.push r else #[r] |> some)
      let m := match node.hi.link with
        | none   => m
        | some _ => m.alter node.hi (if let some l := · then l.push r else #[r] |> some)
      m )
    (HashMap.emptyWithCapacity.insert root #[] : HashMap Ref (Array Ref))

partial
def sweep (mapping : HashMap Ref (Array Ref)) (order : Array Ref) : Array Ref :=
  if mapping.isEmpty then
    order.reverse
  else
    let (next, rest) := mapping.partition (fun _ sources ↦ includes order sources)
    if next.isEmpty
    then sweep next order
    else sweep rest (order.append next.keys.toArray)

end Graph_reorder

def Graph.reorderNodes (numVars : Nat) (nodes : Array Node) (start : Ref) : Graph :=
  let mapping := Graph_reorder.topologicalSort nodes start
  let ordering := Graph_reorder.sweep (/- dbg! s!"Graph.Reorder.reorderNodes.mapping: {mapping}" -/ (mapping.erase start)) #[/- dbg? "Graph.Reorder.reorderNodes.start" -/ start]
  let updatedRef := ordering.toList.zipIdx.map (fun (r, i) ↦ (r, Ref.to i)) |> HashMap.ofList
  let nodes := /- dbg? s!"Graph.Reorder.reorderNodes.updatedRef: {updatedRef}\nGraph.Reorder.reorderNodes.reorder(order): {ordering.toList}\nGraph.Reorder.reorderNodes.reorderedNodes" -/
    (ordering.map
      (fun r ↦
        let n := nodes[r.link.get!]!
        {varId := n.varId, li := updatedRef.getD n.li n.li, hi := updatedRef.getD n.hi n.hi} ) )
  nodes.foldl (·.addNode ·) (Graph.forVars numVars)
