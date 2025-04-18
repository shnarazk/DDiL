import Std.Data.HashMap
import Common.Debug
import Common.DecisionDiagram
import Common.TreeNode
import Common.GraphSerialize
import Common.GraphShape
import Graph.Ref
import Graph.Node

open Std

section defs

variable {γ : Type} [GraphShape γ] (g : γ)

structure Graph where
  nodes       : Array Node
  constant    : Option Bool
  validSize   : Nat := nodes.size
  numVars     : Nat := 0
  validVarIds : ∀ node ∈ nodes, (fun s n ↦ n.varId ≤ s) numVars node
  validRefs   : ∀ node_index ∈ nodes.zipIdx, (fun (n, i) ↦ n.validRef i) node_index

instance : BEq Graph where
  beq g₁ g₂ := g₁.nodes == g₂.nodes && g₁.numVars == g₂.numVars && g₁.constant == g₂.constant

/-- This default value is invalid, becaues it has no constant value and no node. -/
instance : Inhabited Graph where
  default :=
    let nodes : Array Node := #[]
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

instance : Coe Nat Graph where
  coe n := Graph.forVars n

def Graph.asBool (g : Graph) : Option Bool :=
  if g.nodes.isEmpty then g.constant else none

def Graph.addNode (g : Graph) (node : Node) : Graph :=
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
    g'
  else
    dbg
      s!"{ANSI.bold}(Graph.addNode {g.nodes.size} {node}): violation: vi:{node.varId} < g.numVars:{g.numVars} or ref in range: {node.validRef g.nodes.size}{ANSI.unbold}"
      g
      LogKind.error

def Graph.addNode' (g : Graph) (varId : Nat) (li hi : Ref) : Graph :=
  g.addNode {varId, li, hi}

def Graph.ofNodes (nodes : Array Node) : Graph :=
  let numVars : Nat := nodes.map (·.varId) |>.maxD 0
  nodes.foldl (·.addNode ·) (↑numVars : Graph)

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
      let (mapping, node) := match collectFromTreeNode low mapping varId.succ with
        | Collector.bool b => (mapping, {node with li := Ref.bool b})
        | Collector.link m => (m,       {node with li := Ref.to m.size.pred})
      let (mapping, node) := match collectFromTreeNode high mapping varId.succ with
        | Collector.bool b => (mapping, {node with hi := Ref.bool b})
        | Collector.link m => (m,       {node with hi := Ref.to m.size.pred})
      Collector.link (mapping.push node)

end Graph_convert

open Graph_convert in
def Graph.fromTreeNode (tree : TreeNode) : Graph :=
  match collectFromTreeNode tree with
    | Collector.bool b => {(default : Graph) with constant := b}
    | Collector.link m => m.foldl (·.addNode ·) (↑(GraphShape.numberOfVars tree) : Graph)

def Graph.fromNodes (n : Nat) (nodes : Array Node) : Graph :=
  nodes.foldl (·.addNode ·) (↑n : Graph)

/-- make a graph compact, no unused nodes. -/
def Graph.compact (self : Graph) (root : Option Ref := none) : Graph :=
  match root, self.nodes.isEmpty with
  | none, true  => self
  | none, false =>
    Node.compact self.nodes |>.foldl (·.addNode ·) (↑self.numVars : Graph)
  | some _, true  => self
  | some r, false => match r.link with
    | none   => {Graph.fromNodes self.numVars #[] with constant := r.grounded}
    | some _ => Graph.fromNodes self.numVars (Node.compact self.nodes r)

instance : GraphShape Graph where
  numberOfVars  := (·.numVars)
  numberOfNodes := (·.nodes.size)

def Ref.for (g : Graph) : Ref :=
  if g.nodes.isEmpty
  then Ref.bool g.constant.get!
  else Ref.to g.nodes.size.pred

end defs
