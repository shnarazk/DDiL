import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Common.Node

open Std

theorem zero_gt_eq_NeZero (n : Nat) (h : 0 < n) : NeZero n := by
  have : n ≠ 0 := by omega
  exact { out := this }

@[simp]
theorem base_hash_size_eq_two : (HashMap.ofList [(0, Node.isFalse), (1, Node.isTrue)]).size = 2 := by
  apply HashMap.size_ofList
  simp

/-- A set for non-compact indexed nodes
Flow: Array Node → NodeSet → Graph (= NodeSet // compact index family) -/
structure NodeSet extends HashMap Nat Node where
  filled : NeZero toHashMap.size

instance : Inhabited NodeSet where
  default :=
    let nodes : HashMap Nat Node := HashMap.ofList [(0, Node.isFalse), (1, Node.isTrue)]
    have : nodes.size = 2 := by exact base_hash_size_eq_two
    have : nodes.size ≠ 0 := by omega
    have : NeZero nodes.size := by exact {out := this}
    {toHashMap := nodes, filled := this}

#check (default : NodeSet)
#eval! (default : NodeSet).toHashMap

def NodeSet.ofTreeNode' (tree : TreeNode)
    (map : HashMap Nat Node := HashMap.empty) : HashMap Nat Node :=
  match tree with
      | TreeNode.isFalse => map.insert 0 .isFalse
      | TreeNode.isTrue  => map.insert 0 .isTrue
      | TreeNode.node varId low high id =>
        let map₁ := NodeSet.ofTreeNode' low map
        let map₂ := NodeSet.ofTreeNode' high map₁
        map₂.insert id (.node varId low.index high.index)

def NodeSet.ofHashMap (nodes : HashMap Nat Node) : NodeSet :=
  if h : 0 < nodes.size then
    have : NeZero nodes.size := by sorry
    {toHashMap := nodes, filled := this}
  else
    default

def NodeSet.ofTreeNode (tree : TreeNode) : NodeSet :=
  NodeSet.ofHashMap <| NodeSet.ofTreeNode' tree

def NodeSet.compact (self : NodeSet) : NodeSet :=
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
