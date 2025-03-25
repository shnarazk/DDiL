import Std.Data.HashMap
import Graph.Ref
import Graph.Basic

open Std

namespace Graph_reorder

abbrev HashMap := Std.HashMap

def includes (a b : Array Ref) : Bool :=
  b.all (a.contains ·)

partial def topologicalSort (nodes : Array Node) : HashMap Ref (Array Ref) :=
  nodes.zipIdx.foldl
    (fun m (node, i) ↦
      let m := match node.li.link with
        | none => m
        | some _ => m.alter
          node.li
          (fun l ↦ if let some l := l then l.push (Ref.to i) else #[Ref.to i] |> some)
      let m := match node.hi.link with
        | none => m
        | some _ => m.alter
          node.hi
          (fun l ↦ if let some l := l then l.push (Ref.to i) else #[Ref.to i] |> some)
      m )
    (HashMap.empty : HashMap Ref (Array Ref))

partial def sweep (mapping : HashMap Ref (Array Ref)) (order : Array Ref) : Array Ref :=
  if mapping.isEmpty then
    (dbg? "pure order" order).reverse
  else
    let (next, rest) := mapping.partition (fun _ sources ↦ includes order sources)
    if next.isEmpty
    then sweep next order
    else sweep rest (order.append next.keys.toArray)

end Graph_reorder

def Graph.reorderNodes (numVars : Nat) (nodes : Array Node) (start : Ref) : Graph :=
  let mapping := Graph_reorder.topologicalSort (dbg? "nodes" nodes)
  let ordering := Graph_reorder.sweep (dbg! s!"mapping: {mapping.toList}" mapping) #[start]
  let updatedRef := ordering.toList.zipIdx.map (fun (r, i) ↦ (Ref.to i, r)) |> HashMap.ofList
  let nodes := dbg! s!"reorder(order): {ordering.toList}"
    (ordering.map
    (fun to ↦
      let n := nodes[to.link.get!]!
      {varId := n.varId, li := updatedRef.getD n.li n.li, hi := updatedRef.getD n.hi n.hi} ) )
  nodes.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars numVars)
