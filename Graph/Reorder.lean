import Std.Data.HashMap
import Graph.Ref
import Graph.Basic

open Std

namespace Graph_reorder

abbrev HashMap := Std.HashMap

partial def topologicalSort (nodes : Array Node) : HashMap Ref (Array Ref) :=
  nodes.zipIdx.foldl
    (fun m (node, i) ↦
      let m := match node.li.link with
        | none => m
        | some _ => m.alter
          (Ref.to i)
          (fun l ↦ if let some l := l then l.push node.li else #[node.li] |> some)
      let m := match node.hi.link with
        | none => m
        | some _ => m.alter
          (Ref.to i)
          (fun l ↦ if let some l := l then l.push node.hi else #[node.hi] |> some)
      m )
    (HashMap.empty : HashMap Ref (Array Ref))

end Graph_reorder

def Graph.reorderNodes (_numVars : Nat) (nodes : Array Node) : Graph :=
  let mapping := Graph_reorder.topologicalSort (dbg? "nodes" nodes)
  dbg! s!"reorder: {mapping.toList}" default
