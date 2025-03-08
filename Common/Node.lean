import Common.TreeNode
import Common.GraphShape
import Mathlib.Tactic

open Std

section proofs

theorem array_element_induction {α : Type} (p : α → Nat) (a : Array α) (h : ∀ x ∈ a, p x < a.size)
    (b : α) (hb : p b < (a.push b).size) :
    ∀ x ∈ a.push b, p x < (a.push b).size := by
  have tr (n : α) {s : Nat} : p n < s → p n < s + 1 := by
    exact Nat.lt_succ_of_lt
  simp [Array.push]
  intro x h'
  rcases h' with h₁ | h₂
  {rcases h x h₁ with h₂ ; exact tr x (h x h₁)}
  {simp [h₂] at * ; exact hb}

#eval ∀ i < 4, i < 8

theorem le_induction (n : Nat) : ∀ i : Nat, i < n + 1 → i < n ∨ i == n := by
  intro i h
  simp
  exact Nat.lt_succ_iff_lt_or_eq.mp h

/-
theorem array_index_induction {α : Type} (a : Array α) (p : α → Option Nat) (b : α)
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
-/

end proofs

section defs

variable {γ : Type} [GraphShape γ] (g : γ)

structure Ref where
  grounded : Bool
  link : Option Nat
deriving BEq, Hashable

instance : Inhabited Ref where
  default := {grounded := false, link := none}

  instance : ToString Ref where
    toString self := match self with
      | {grounded := false, link := none}   => "⊥"
      | {grounded := true , link := none}   => "⊤"
      | {grounded := true , link := some i} => s!"to:{i}"
      | {grounded := false, link := some i} => s!"to:{i}"

def Ref.bool (b : Bool) : Ref := {grounded := b, link := none}
def Ref.to (n : Nat) : Ref := {grounded := false, link := some n}

def Ref.isSmaller (self : Ref) (n : Nat) : Bool := match self.link with
  | none => true
  | some i => i < n

structure Node where
  varId : Nat
  li : Ref
  hi : Ref
deriving BEq, Hashable

instance : ToString Node where
  toString self :=
    let li := toString self.li
    let hi := toString self.hi
    if li == hi then
      s!"Node(var:{self.varId} ↦ {li})"
    else
      s!"Node(var:{self.varId}, li:{self.li}, hi:{self.hi})"

def Node.validRef (self : Node) (pos : Nat) : Bool :=
  match self.li.link, self.hi.link with
    | some l, some h => l < pos ∧ h < pos
    | some l, none   => l < pos
    | none  , some h => h < pos
    | none  , none   => true

/-
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
  validSize : Nat := nodes.size
  numVars : Nat := 0
  validVarIds : ∀ node ∈ nodes, (fun s n ↦ n.varId ≤ s) numVars node
  validRefs : ∀ node_index ∈ nodes.zipIdx, (fun (n, i) ↦ n.validRef i) node_index

instance : Inhabited Graph where
  default :=
    let nodes : Array Node := Array.empty
    have nodes₀ : nodes.size = 0 := rfl
    have nodes_def : nodes = #[] := by exact rfl
    have vi : ∀ node ∈ nodes, node.varId ≤ 0 := by
      rintro node₀ h₀
      simp [nodes_def] at h₀
    have ordered : ∀ node ∈ nodes.zipIdx, (fun (n, i) ↦ n.validRef i) node := by
      rintro i h
      simp [nodes_def] at h
    { nodes := nodes,
      numVars := 0,
      validVarIds := vi,
      constant := some false,
      validSize := 0,
      validRefs := ordered,
    }

instance : ToString Graph where
  toString g := s!"Graph: {g.nodes}"

def Graph.forVars (n : Nat) : Graph :=
 let g : Graph := default
  have vi : ∀ node ∈ g.nodes, node.varId ≤ n := by
      rintro node₀ h₀
      have : g.nodes = #[] := by exact rfl
      rw [this] at h₀
      simp at h₀
  { g with
    numVars := n
    validVarIds := vi }

def Graph.addNode (g : Graph) (vi : Nat) (li hi : Ref) : Graph × Nat :=
  let node := { varId := vi, li := li, hi := hi }
  let nodes := g.nodes.push node
  if h : vi ≤ g.numVars ∧ node.validRef g.nodes.size then
    let g' : Graph := { g with
      nodes := nodes
      validSize := nodes.size
      validVarIds := by
        simp [nodes]
        rintro n (h₀ | h₁)
        {exact g.validVarIds n h₀}
        {simp [h₁, node] ; exact h.left}
      validRefs := by
        simp [nodes]
        simp [Array.zipIdx]
        have base : ∀ node ∈ g.nodes.zipIdx, (fun (n, i) ↦ n.validRef i) node := by
          exact g.validRefs
        simp [Array.zipIdx] at base
        intro n i j
        rcases j with j | j
        {
          rcases base n i with base₀
          rcases j with ⟨jg, k⟩
          rcases base₀ i jg k with base₁
          simp at base₁
          exact base₁ }
        {
          simp [j.left, j.right]
          exact h.right }
    }
    (g', nodes.size - 1)
  else (g, g.nodes.size)

end defs
