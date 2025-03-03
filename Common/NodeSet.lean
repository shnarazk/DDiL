import Std.Data.HashMap
import Common.Node

open Std

/-- A set for non-compact indexed nodes
Flow: Array Node → NodeSet → Graph (= NodeSet // compact index family)
-/
structure NodeSet extends HashMap Nat Node where
  filled : NeZero toHashMap.size

instance : Inhabited NodeSet where
  default :=
    let nodes : HashMap Nat Node := HashMap.empty.insertMany [(0, Node.isFalse), (1, Node.isTrue)]
    have : nodes.size = 2 := by sorry
    have : nodes.size ≠ 0 := by sorry
    have : NeZero nodes.size := by sorry -- isorry
    { toHashMap := nodes, filled := this  }

#check (default : NodeSet)
#eval! (default : NodeSet).toHashMap

namespace NodeSet

def ofHashMap (nodes : HashMap Nat Node) : NodeSet :=
  if h : 0 < nodes.size then
      have : NeZero nodes.size := by sorry
      { toHashMap := nodes, filled := this }
    else
      default

def compact (self : NodeSet) : NodeSet :=
  let ids : HashMap Nat Nat := HashMap.ofList <| self.keys.zipIdx
  self.toList
    |>.map
      (fun (key, node) ↦ match node with
        | Node.isFalse => (0, Node.isFalse)
        | Node.isTrue => (1, Node.isTrue)
        | Node.node vi li hi => (ids[key]!, Node.node vi ids[li]! ids[hi]!) )
    |> HashMap.ofList
    |> NodeSet.ofHashMap

#eval! (default : NodeSet).compact

end NodeSet
