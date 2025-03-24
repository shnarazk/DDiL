import Std.Data.HashMap
import Graph.Ref
import Graph.Basic

open Std

namespace Graph_reorder

abbrev HashMap := Std.HashMap

partial def topologicalSort (nodes : Array Node) (r : Ref)
    (mapping : HashMap Ref Nat := HashMap.empty) (ix : Nat := 0)
    : HashMap Ref Nat × Nat :=
  let ordering := nodes.zipIdx.foldl
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
  (mapping, ix)


end Graph_reorder

def Graph.reorderNodes (numVars : Nat) (nodes : Array Node) : Graph := default
