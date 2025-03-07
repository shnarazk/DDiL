import Common.TreeNode
import Common.GraphShape
import Mathlib.Tactic

open Std

section proofs

theorem array_element_induction {α : Type} (p : α → Prop) (a : Array α) (h : ∀ x ∈ a, p x)
    (b : α) (hb : p b) :
    ∀ x ∈ a.push b, p x := by
  simp [Array.push]
  intro x h'
  rcases h' with h₁ | h₂
  { rcases h x h₁ with h₂ ; exact h₂ }
  { simp [h₂] ; exact hb }

#eval ∀ i < 4, i < 8

theorem le_induction (n : Nat) : ∀ i : Nat, i < n + 1 → i < n ∨ i == n := by
  intro i h
  simp
  exact Nat.lt_succ_iff_lt_or_eq.mp h

theorem array_index_induction {α : Type} (a : Array α) (p : α → Prop) (b : α)
    (h : ∀ i < a.size, match a[i]? with | none => true | some e => p e) (pb : p b) :
    ∀ i < (a.push b).size, match (a.push b)[i]? with | none => true | some e => p e := by
  have {q : Nat → Prop} : (∀ i < (a.push b).size, q i) → (∀ i < (a.push b).size - 1, q i) ∨ (q (a.push b).size) := by
    have : (a.push b).size = a.size + 1 := by simp [Array.push]
    simp [this]
    intro x
    constructor
    { intro j hj
      rcases x j with hj'
      have : j < a.size + 1 := by exact Nat.lt_add_right 1 hj
      exact hj' this }
  intro i h'
  rcases Nat.lt_trichotomy i a.size with h₀ | h' | hp
  { rcases h i h₀ with h₁
    have get₀ : i < a.size → a[i]? = some a[i] := by
      intro h
      exact Array.getElem?_eq_getElem h₀
    rcases get₀ h₀ with get₀
    have get₁ : i < a.size → (a.push b)[i]? = some a[i] := by
      intro h
      exact Array.getElem?_push_lt a b i h
    rcases get₁ h₀ with get₁
    simp [get₀, get₁]
    simp [get₀, get₁] at h₁
    exact h₁ }
  { simp [h'] ; exact pb }
  { have : (a.push b).size = a.size + 1 := by exact Array.size_push a b
    simp [this] at h'
    have : i ≤ a.size := by exact Nat.le_of_lt_succ h'
    have : ¬a.size < i := by exact Nat.not_lt.mpr this
    contradiction }

end proofs

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

def varIndexIsOrdered₀ (nodes : Array Node) (vi : Nat) : Bool :=
  if h : vi < nodes.size then
    match (nodes[vi]'h).li.link with
    | none => true
    | some i => match nodes[i]? with
      | none => false
      | some node => node.varId < vi
  else
    false

def varIndexIsOrdered₁ (nodes : Array Node) (vi : Nat) : Bool :=
  if h : vi < nodes.size then
    match (nodes[vi]'h).li.link with
    | none => true
    | some i => match nodes[i]? with
      | none => false
      | some node => node.varId < vi
  else
    false

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

structure Graph where
  nodes : Array Node
  constant : Option Bool
  validSize : nodes.size = 0
  validVarIds : ∀ node ∈ nodes, node.varId < nodes.size
  validRefs : ∀ node ∈ nodes, node.validRef nodes.size
  ordered_li : ∀ i < nodes.size, varIndexIsOrdered₀ nodes i
  ordered_hi : ∀ i < nodes.size, varIndexIsOrdered₁ nodes i

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
    have li : ∀ i < nodes.size, varIndexIsOrdered₀ nodes i := by
      rintro i h
      simp [nodes_def] at h
    have hi : ∀ i < nodes.size, varIndexIsOrdered₁ nodes i := by
      rintro i h
      simp [nodes_def] at h
    { nodes := nodes,
      validVarIds := vi
      constant := some false,
      validSize := rfl,
      validRefs := refs,
      ordered_li := li,
      ordered_hi := hi
    }

def Graph.addNewNode (g : Graph) (vi : Nat) (li hi : Ref) : Graph × Nat :=
  let node := { varId := vi, li := li, hi := hi }
  let nodes := g.nodes.push node
  let g' : Graph := { g with
      nodes := nodes
      validVarIds := by sorry
  }
  (g', nodes.size - 1)

end defs
