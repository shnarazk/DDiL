import Std.Data.HashMap
import Common.Debug
import Common.DecisionDiagram
import Common.TreeNode
import Common.GraphSerialize
import Common.GraphShape
-- import Common.Basic
import Graph.Ref
import Graph.Node

open Std

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

/-- This default value is invalid, becaues it has no constant value and no node. -/
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
      constant := none,
      validSize := 0,
      validRefs := ordered, }

instance : ToString Graph where
  toString g := match g.constant with
    | none   => s!"Graph {g.numVars}: {g.nodes}"
    | some b => s!"Graph {g.numVars}: {b} (|nodes| = {g.nodes.size})"

def Graph.forVars (n : Nat) : Graph :=
 let g : Graph := default
  have vi : ∀ node ∈ g.nodes, node.varId ≤ n := by
    rintro node₀ h₀
    have : g.nodes = #[] := by exact rfl
    rw [this] at h₀
    simp at h₀
  {g with numVars := n, validVarIds := vi}

def Graph.asBool (g : Graph) : Option Bool :=
  if g.nodes.isEmpty then g.constant else none

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
        { rcases base n i with base₀
          rcases j with ⟨jg, k⟩
          rcases base₀ i jg k with base₁
          simp at base₁
          exact base₁ }
        { simp [j.left, j.right]
          exact h.right } }
    (g', nodes.size - 1)
  else
    dbg
      s!"{ANSI.bold}(Graph.addNode {g.nodes.size} {node}): violation: vi:{node.varId} < g.numVars:{g.numVars} or ref in range: {node.validRef g.nodes.size}{ANSI.unbold}"
      (g, g.nodes.size)
      LogKind.error

def Graph.addNode' (g : Graph) (vi : Nat) (li hi : Ref) : Graph × Nat :=
  g.addNode {varId := vi, li := li, hi := hi}

def Graph.ofNodes (nodes : Array Node) : Graph :=
  let numVars := nodes.map (·.varId) |>.maxD 0
  nodes.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars numVars)

namespace Graph_convert

inductive Collector where
  | bool (val : Bool)
  | link (mapping : Array Node)

instance : Inhabited Collector where
  default := Collector.link #[]

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

end Graph_convert

open Graph_convert in
def Graph.fromTreeNode (tree : TreeNode) : Graph :=
  match collectFromTreeNode tree with
    | Collector.bool b => {(default : Graph) with constant := b}
    | Collector.link m => m.foldl
      (fun g node => g.addNode node |>.fst)
      (Graph.forVars (GraphShape.numberOfVars tree))

def Graph.fromNodes (n : Nat) (nodes : Array Node) : Graph :=
  nodes.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars n)

/-
namespace Graph_compact

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

def compact (nodes : Array Node) (root : Ref := Ref.last nodes) : Array Node :=
  let used : Array Ref := usedNodes nodes root
    |>.toArray
    |>.insertionSort (fun a b => a < b)
  let mapping : HashMap Ref Ref := used.zipIdx.map (fun (n, i) ↦ (n, Ref.to i))
    |>.toList
    |>HashMap.ofList
  used.map
    (fun r ↦
      if let some i := r.link then
        let node := nodes[i]!
        {node with li := mapping.getD node.li node.li, hi := mapping.getD node.hi node.hi}
      else
        (default : Node) )

end Graph_compact
-/

/-- make a graph compact, no unused nodes. -/
def Graph.compact (self : Graph) (root : Option Ref := none) : Graph :=
  match root, self.nodes.isEmpty with
  | none, true => self
  | none, false =>
    Node.compact self.nodes
      |>.foldl (fun g n ↦ g.addNode n |>.fst) (Graph.forVars self.numVars)
  | some _, true => self
  | some r, false => match r.link with
    | none   => {Graph.fromNodes self.numVars #[] with constant := r.grounded}
    | some _ => Graph.fromNodes self.numVars (Node.compact self.nodes r)

instance : GraphShape Graph where
  numberOfVars := (·.numVars)
  numberOfNodes := (·.nodes.size)

namespace Graph_count

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
partial def linearCount (g : Graph) (counter : Std.HashMap Ref Nat) (r : Ref) : Std.HashMap Ref Nat × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then
     (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a) := linearCount g counter node.li
      let (counter, b) := linearCount g counter node.hi
      (counter.insert r (a + b), (a + b))

end Graph_count

/--
Returns the number of satisfying assignments for the given TreeNode.
This is the number of paths. -/
def Graph.numSatisfies (self : Graph) : Nat :=
    Graph_count.linearCount self Std.HashMap.empty (Ref.to (self.nodes.size - 1)) |>.snd

def Ref.for (g : Graph) : Ref :=
  if g.nodes.isEmpty then
    Ref.bool (g.constant.getD false)
  else
    Ref.to g.nodes.size.pred

end defs
