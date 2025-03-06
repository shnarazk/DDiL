import Std.Data.HashMap
import Std.Data.HashSet
import Common.TreeNode

open Std

structure Ref (o : Nat) where
  grounded : Bool
  link : Option (Fin o)

instance {o : Nat} : Inhabited (Ref o) where
  default := { grounded := false, link := none }

def Ref.isSmaller {r : Nat} (self : Ref r) (n : Nat) : Bool := match self.link with
  | none => true
  | some i => i < n

structure Node (n o : Nat) where
  varId : Fin n
  li : Ref o
  hi : Ref o

def varIndexIsOrdered {n o : Nat} (nodes : Array (Node n o)) (vi : Nat) (r : Ref o) : Bool :=
  match r.link with
  | none => true
  | some i => match nodes[i.val]? with
    | none => false
    | some node => node.varId < vi

theorem hj {n r : Nat} (nodes : Array (Node n r)) (i : Nat) (h : i < nodes.size) :
  varIndexIsOrdered nodes nodes[i].varId.val nodes[i].li ∧
    varIndexIsOrdered nodes nodes[i].varId.val nodes[i].hi
    := by
  sorry

structure Graph (n o : Nat) where
  nodes : Array (Node n o)
  constant : Option Bool
  validSize : nodes.size = 0
  ordered_li : ∀i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).li.isSmaller i
  ordered_hi : ∀i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).hi.isSmaller i

instance {n o : Nat} : Inhabited (Graph n o) where
  default :=
    let nodes : Array (Node n o) := Array.empty
    have nodes₀ : nodes.size = 0 := rfl
    have li : ∀i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).li.isSmaller i := by
      simp [nodes₀]
    have hi : ∀i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).hi.isSmaller i := by
      simp [nodes₀]
    { nodes := nodes,
      constant := some false,
      validSize := rfl,
      ordered_li := li,
      ordered_hi := hi }

-----------------------------------
/-
instance : Inhabited Node where
  default := .isFalse

def Node.toVarId (self : Node) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 0
  | .node varId _ _ => varId

def Node.newNode (varId low high: Nat) : Node :=
  .node varId low high

instance : ToString Node where
  toString (n : Node) : String := match n with
    | .isFalse => "#false"
    | .isTrue  => "#true"
    | .node varId 0 0 => s!"[v:{varId}=false]"
    | .node varId 0 1 => s!"[v:{varId}]"
    | .node varId 1 0 => s!"[v:-{varId}]"
    | .node varId 1 1 => s!"[v:{varId}=true]"
    | .node varId 0 h => s!"[v:{varId} l:false h:{h}]"
    | .node varId 1 h => s!"[v:{varId} l:true h:{h}]"
    | .node varId l 0 => s!"[v:{varId} l:{l} h:false]"
    | .node varId l 1 => s!"[v:{varId} l:{l} h:true]"
    | .node varId l h => s!"[v:{varId} l:{l} h:{h}]"

def Node.newConstant (value : Bool) : Node := match value with
  | false => .isFalse
  | true  => .isTrue

def Node.isConstant (self : Node) : Option Bool := match self with
  | .isFalse => some false
  | .isTrue  => some true
  | .node _ _ _ => none

def Node.ofTreeNode' (tree : TreeNode)
    (map : HashMap Nat Node := HashMap.empty) : HashMap Nat Node :=
  match tree with
    | TreeNode.isFalse => map.insert 0 .isFalse
    | TreeNode.isTrue  => map.insert 0 .isTrue
    | TreeNode.node varId low high id =>
      let map₁ := Node.ofTreeNode' low map
      let map₂ := Node.ofTreeNode' high map₁
      map₂.insert id (.node varId low.index high.index)

def Node.ofTreeNode (tree : TreeNode) : Array Node :=
  let mapping := Node.ofTreeNode' tree
  (Array.range mapping.size).map (mapping.getD · default)
-/
