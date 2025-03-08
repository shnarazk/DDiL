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

/--
Reference to other node or a constant, having `grounded` and `link`.
There are two constructors: `Ref.bool` and `Ref.to`. -/
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

/--
Node representation for graph, having `varId`, `li`, and `hi`. -/
structure Node where
  varId : Nat
  li : Ref
  hi : Ref
deriving BEq, Hashable

instance : Inhabited Node where
  default := { varId := 0, li := default, hi := default }

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

instance : GraphShape Graph where
  numberOfVars := (·.numVars)
  numberOfNodes := (·.nodes.size)

namespace convert

inductive Collector where
  | bool (val : Bool)
  | link (mapping : HashMap Nat Node)

instance : Inhabited Collector where
  default := Collector.link (HashMap.empty)

def collectFromTreeNode (tree : TreeNode)
    (mapping : HashMap Nat Node := HashMap.empty)
    (varId : Nat := 1)
    : Collector :=
  match tree with
    | TreeNode.isFalse => Collector.bool false
    | TreeNode.isTrue  => Collector.bool true
    | TreeNode.node low high id =>
      let node : Node := {(default : Node) with varId}
      let (mapping, node) := match collectFromTreeNode low mapping (varId + 1) with
        | Collector.bool b => (mapping, {node with li := Ref.bool b})
        | Collector.link m => (m,       {node with li := Ref.to (m.size - 1)})
      let (mapping, node) := match collectFromTreeNode high mapping (varId + 1) with
        | Collector.bool b => (mapping, {node with hi := Ref.bool b})
        | Collector.link m => (m,       {node with hi := Ref.to (m.size - 1)})
      Collector.link (mapping.insert id node)

def toCompactArray (h : HashMap Nat Node) : Array Node :=
    (Array.range h.size).map (h.getD · default)

end convert

open convert in
def Graph.fromTreeNode (tree : TreeNode) : Graph :=
  match collectFromTreeNode tree with
    | Collector.bool b => {(default : Graph) with constant := b}
    | Collector.link m => m.toList.mergeSort (fun a b ↦ a.fst < b.fst)
      |>.foldl
        (fun g (_, node) => g.addNode node.varId node.li node.hi |>.fst)
        (default : Graph)

end defs
