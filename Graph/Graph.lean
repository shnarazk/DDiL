import Std.Data.HashMap
import Common.Debug
import Common.DecisionDiagram
import Common.TreeNode
import Common.GraphShape
import Graph.Ref
import Graph.Node
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

structure Graph where
  nodes : Array Node
  constant : Option Bool
  validSize : Nat := nodes.size
  numVars : Nat := 0
  validVarIds : ∀ node ∈ nodes, (fun s n ↦ n.varId ≤ s) numVars node
  validRefs : ∀ node_index ∈ nodes.zipIdx, (fun (n, i) ↦ n.validRef i) node_index

instance : BEq Graph where
  beq g₁ g₂ := g₁.nodes == g₂.nodes && g₁.numVars == g₂.numVars && g₁.constant == g₂.constant

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

def Graph.addNode (g : Graph) (node : Node) : Graph × Nat :=
  let nodes := g.nodes.push node
  if h : node.varId ≤ g.numVars ∧ node.validRef g.nodes.size then
    let g' : Graph := { g with
      nodes := nodes
      validSize := nodes.size
      validVarIds := by
        simp [nodes]
        rintro n (h₀ | h₁)
        {exact g.validVarIds n h₀}
        {simp [h₁] ; exact h.left}
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
  else
    dbg
      s!"{g.nodes.size}:{node} violation: vi:{node.varId} < g.numVars:{g.numVars} or ref:{node.validRef g.nodes.size}"
      (g, g.nodes.size)
      LogKind.error

def Graph.addNode' (g : Graph) (vi : Nat) (li hi : Ref) : Graph × Nat :=
  g.addNode {varId := vi, li := li, hi := hi}

namespace convert

inductive Collector where
  | bool (val : Bool)
  | link (mapping : Array Node)

instance : Inhabited Collector where
  default := Collector.link (#[])

def collectFromTreeNode (tree : TreeNode) (mapping : Array Node := #[]) (varId : Nat := 1)
    : Collector :=
  match tree with
    | TreeNode.isFalse => Collector.bool false
    | TreeNode.isTrue  => Collector.bool true
    | TreeNode.node low high _ =>
      let node : Node := {(default : Node) with varId}
      let (mapping, node) := match collectFromTreeNode low mapping (varId + 1) with
        | Collector.bool b => (mapping, {node with li := Ref.bool b})
        | Collector.link m => (m,       {node with li := Ref.to (m.size - 1)})
      let (mapping, node) := match collectFromTreeNode high mapping (varId + 1) with
        | Collector.bool b => (mapping, {node with hi := Ref.bool b})
        | Collector.link m => (m,       {node with hi := Ref.to (m.size - 1)})
      Collector.link (mapping.push node)

end convert

open convert in
def Graph.fromTreeNode (tree : TreeNode) : Graph :=
  match collectFromTreeNode tree with
    | Collector.bool b => {(default : Graph) with constant := b}
    | Collector.link m => m.foldl
        (fun g node => g.addNode node |>.fst)
        (Graph.forVars (GraphShape.numberOfVars tree))

def Graph.fromNodes (n : Nat) (nodes : Array Node) : Graph :=
  nodes.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars n)

def Graph.dumpAsDot (self : Graph) (path : String) : IO String := do
  let buffer := "digraph regexp {
    fontname=\"Helvetica,Arial,sans-serif\"
    node [fontname=\"Helvetica,Arial,sans-serif\"]
    edge [fontname=\"Helvetica,Arial,sans-serif\", color=blue]
      0 [style=filled, fillcolor=\"gray80\",label=\"false\",shape=\"box\"];
      1 [style=filled, fillcolor=\"gray95\",label=\"true\",shape=\"box\"];
  "
  let nodes := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦  s!"  {i + 2} [label=\"{node.varId}\"];\n")
    |> String.join
  let edges := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦
        let li := match node.li.link, node.li.grounded with
          | none, false => 0
          | none, true  => 1
          | some i, _   => i + 2
        let hi := match node.hi.link, node.hi.grounded with
          | none, false => 0
          | none, true  => 1
          | some i, _   => i + 2
        if li == hi then
              s!" {i + 2} -> {li} [color=black,penwidth=2];\n"
            else
              s!" {i + 2} -> {li} [color=red,style=\"dotted\"];\n" ++
              s!" {i + 2} -> {hi} [color=blue];\n" )
    |> String.join
  IO.FS.writeFile path (buffer ++ "\n" ++ nodes ++ "\n" ++ edges ++ "\n}\n")
  return path

def Graph.dumpAsPng (self : Graph) (path : String) : IO String := do
  try
    let gv := s!"{path}.gv"
    let _ ← self.dumpAsDot gv
    let _ ← IO.Process.run { cmd := "dot", args := #["-T", "png", "-o", path, gv]}
    IO.FS.removeFile gv
    return path
  catch e =>
    return s!"Error dumping graph to PNG: {e}"

namespace compacting

partial
def usedNodes (nodes : Array Node) (root : Ref) (mapping : HashSet Ref := HashSet.empty) : HashSet Ref :=
  if let some (i) := root.link then
    if mapping.contains root then
      mapping
    else
      let node : Node := nodes[i]!
      usedNodes nodes node.li (mapping.insert root) |> usedNodes nodes node.hi
  else
    mapping

def compact (nodes : Array Node) : Array Node :=
  let used : Array Ref := usedNodes nodes (Ref.to (nodes.size - 1))
    |>.toArray
    |>.insertionSort (fun a b => a < b)
  let mapping : HashMap Ref Ref := used
    |>.zipIdx
    |>.map (fun (n, i) ↦ (n, Ref.to i))
    |>.toList
    |>HashMap.ofList
  used.map
    (fun r ↦
      if let some i := r.link
      then
        let node := nodes[i]!
        { node with
          li := mapping.getD node.li node.li,
          hi := mapping.getD node.hi node.hi }
      else
        (default : Node) )

end compacting

/-- make a graph compact, no unused nodes. -/
def Graph.compact (self : Graph) : Graph :=
  compacting.compact self.nodes
    |>.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars self.numVars)

instance : GraphShape Graph where
  numberOfVars := (·.numVars)
  numberOfNodes := (·.nodes.size)
  dumpAsDot := Graph.dumpAsDot
  dumpAsPng := Graph.dumpAsPng

namespace graph_counting

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
partial def linearCount (g : Graph) (counter : Std.HashMap Ref Nat) (r : Ref) : Std.HashMap Ref Nat × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a) := linearCount g counter node.li
      let (counter, b) := linearCount g counter node.hi
      (counter.insert r (a + b), (a + b))

end graph_counting

/--
Returns the number of satisfying assignments for the given TreeNode.
This is the number of paths. -/
def Graph.numSatisfies (self : Graph) : Nat :=
    graph_counting.linearCount self Std.HashMap.empty (Ref.to (self.nodes.size - 1)) |>.snd

instance : DecisionDiagram Graph where
  numberOfSatisfyingPaths (g : Graph) := g.numSatisfies
  apply (_f : MergeFunction) (g _ : Graph) : Graph := g
  compose (self _other : Graph) (_varId : Nat) : Graph := self

end defs
