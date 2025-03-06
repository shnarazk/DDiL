import Common.TreeNode
import Common.GraphShape

open Std

section defs

variable {γ : Type} [GraphShape γ] (g : γ)

structure Ref where
  grounded : Bool
  link : Option Nat

instance : Inhabited Ref where
  default := { grounded := false, link := none }

def Ref.isSmaller (self : Ref) (n : Nat) : Bool := match self.link with
  | none => true
  | some i => i < n

structure Node where
  varId : Nat
  li : Ref
  hi : Ref

def Node.validRef (self : Node) (pos : Nat) : Bool :=
  match self.li.link, self.hi.link with
    | some l, some h => l < pos ∧ h < pos
    | some l, none   => l < pos
    | none  , some h => h < pos
    | none  , none   => true

def varIndexIsOrdered (nodes : Array Node) (vi : Nat) (r : Ref) : Bool :=
  match r.link with
  | none => true
  | some i => match nodes[i]? with
    | none => false
    | some node => node.varId < vi

structure Graph where
  nodes : Array Node
  constant : Option Bool
  validSize : nodes.size = 0
  validVarIds : ∀ node ∈ nodes, node.varId < nodes.size
  validRefs : ∀ node ∈ nodes, node.validRef nodes.size
  -- ordered_li : ∀ i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).li.isSmaller i
  -- ordered_hi : ∀ i < nodes.size, (nodes[i]'(by sorry : i < nodes.size)).hi.isSmaller i

instance : Inhabited Graph where
  default :=
    let nodes : Array Node := Array.empty
    have nodes₀ : nodes.size = 0 := rfl
    have nodes_def : nodes = #[] := by exact rfl
    have vi : ∀ node ∈ nodes, node.varId < nodes.size := by
      rintro node₀ h₀
      simp [nodes_def] at h₀
    have refs : ∀ node ∈ nodes, node.validRef nodes.size := by
      rintro node₀ h₀
      simp [nodes_def] at h₀
    { nodes := nodes,
      validVarIds := vi
      constant := some false,
      validSize := rfl,
      validRefs := refs,
      -- ordered_li := li,
      -- ordered_hi := hi
    }

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
end defs
