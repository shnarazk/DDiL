import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Common.Node

open Std

section Proofs

def base : HashMap Nat Node := HashMap.ofList [(0, Node.isFalse), (1, Node.isTrue)]

theorem base_hash_has_zero : 0 ∈ base := by
  rw [base]
  simp

theorem base_hash_has_one : 1 ∈ base := by
  rw [base]
  simp

theorem zero_gt_eq_NeZero (n : Nat) (h : 0 < n) : NeZero n := by
  have : n ≠ 0 := by omega
  exact { out := this }

@[simp]
theorem base_hash_size_eq_two : base.size = 2 := by
  apply HashMap.size_ofList
  simp

theorem base_hash_is_bounded : ∀ k ∈ base, k < base.size := by
  simp
  sorry

theorem base_hash_has_no_hole : ∀ k < base.size, k ∈ base := by
  simp
  intro n h
  have : n = 0 ∨ n = 1 := by omega
  rcases this with h0 | h1
  {rw [h0] ; exact base_hash_has_zero}
  {rw [h1] ; exact base_hash_has_one}

end Proofs

/-- A HashMap with nifty properties
Note: It might be non-compact.
Flow: Array Node → NodeSet → Graph (= NodeSet // compact index family) -/
structure NodeSet extends HashMap Nat Node where
  filled : NeZero toHashMap.size
  bounded : ∀k ∈ toHashMap, k < toHashMap.size
  no_hole : ∀k < toHashMap.size, k ∈ toHashMap

instance : Inhabited NodeSet where
  default :=
    let nodes : HashMap Nat Node := HashMap.ofList [(0, Node.isFalse), (1, Node.isTrue)]
    have : nodes.size = 2 := by exact base_hash_size_eq_two
    have : nodes.size ≠ 0 := by omega
    have filled : NeZero nodes.size := by exact {out := this}
    have : nodes.keys = [0, 1] := by sorry
    { toHashMap := nodes
      filled := filled
      bounded := by sorry
      no_hole := by sorry
    }

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
  if h : 0 < nodes.size ∧ (∀k ∈ nodes.keys, k < nodes.size) ∧ (∀ k < nodes.size, k ∈ nodes)
  then
    have : NeZero nodes.size := by
      exact zero_gt_eq_NeZero nodes.size h.left
    {toHashMap := nodes, filled := this, bounded := h.right.left, no_hole := h.right.right}
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
