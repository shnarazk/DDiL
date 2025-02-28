import Std.Data.HashMap
import Std.Data.HashSet
import Common.Node

open Std

structure Graph where
  nodes : Array Node
  root : Fin (nodes.size)
  filled : NeZero nodes.size
deriving Hashable, Repr

instance : BEq Graph where
  beq g₁ g₂ := (g₁.root.val == g₂.root.val) && (g₁.nodes == g₂.nodes)

instance : Inhabited Graph where
  default := {
    nodes := #[.isFalse, .isTrue],
    root := Fin.ofNat' 2 0,
    filled := by exact Nat.instNeZeroSucc }

instance : ToString (Graph × Nat)  where
  toString gn : String :=
    let (g, id) := gn
    match g.nodes[@Fin.ofNat' g.nodes.size g.filled id] with
    | .isFalse => "[false]"
    | .isTrue  => "[true]"
    | .node varId 0 0 => s!"[#{id} v:{varId}=false]"
    | .node varId 0 1 => s!"[#{id} v:{varId}]"
    | .node varId 1 0 => s!"[#{id} v:-{varId}]"
    | .node varId 1 1 => s!"[#{id} v:{varId}=true]"
    | .node varId 0 h => s!"[#{id} v:{varId} l:false h:{h}]"
    | .node varId 1 h => s!"[#{id} v:{varId} l:true h:{h}]"
    | .node varId l 0 => s!"[#{id} v:{varId} l:{l} h:false]"
    | .node varId l 1 => s!"[#{id} v:{varId} l:{l} h:true]"
    | .node varId l h => s!"[#{id} v:{varId} l:{l} h:{h}]"

def Graph.lowIndexOf (g : Graph) (n : Node) : Fin g.nodes.size := match n with
  | .isFalse    => @Fin.ofNat' g.nodes.size g.filled 0
  | .isTrue     => @Fin.ofNat' g.nodes.size g.filled 1
  | .node _ l _ => @Fin.ofNat' g.nodes.size g.filled l

  def Graph.highIndexOf (g : Graph) (n : Node) : Fin g.nodes.size := match n with
    | .isFalse    => @Fin.ofNat' g.nodes.size g.filled 0
    | .isTrue     => @Fin.ofNat' g.nodes.size g.filled 1
    | .node _ _ h => @Fin.ofNat' g.nodes.size g.filled h

def Graph.is_congruent₁ (limit : Nat) (g₁ g₂ : Graph)
    (n₁ : Fin g₁.nodes.size) (n₂ : Fin g₂.nodes.size) : Bool :=
  match limit, g₁.nodes[n₁], g₂.nodes[n₂] with
  | 0, _, _ => false
  | _, .isFalse, .isFalse => true
  | _, .isTrue , .isTrue  => true
  | k + 1, n₁@(.node varId1 _ high1), n₂@(.node varId2 _ high2) =>
    varId1 = varId2
    && Graph.is_congruent₁ k g₁ g₂ (g₁.lowIndexOf n₁) (g₂.lowIndexOf n₂)
    && Graph.is_congruent₁ k g₁ g₂ (g₁.highIndexOf n₁) (g₂.highIndexOf n₂)
  | _, _, _ => false

def Graph.is_congruent (a b : Graph) : Bool :=
  Graph.is_congruent₁ (max a.nodes.size b.nodes.size) a b a.root b.root

def Graph.constant (_ : Graph) (value : Bool) : Node := match value with
  | false => .isFalse
  | true  => .isTrue

def Graph.addNewNode (self : Graph) (varId : Nat) (li hi : Nat) : Nat × Graph :=
  let node := .node varId li hi
  let nodes := self.nodes.push node
  have : NeZero nodes.size := by
    have : nodes.size = self.nodes.size + 1 := by rw [Array.size_push]
    rw [this]
    exact Nat.instNeZeroSucc
  (nodes.size - 1, { self with
    nodes := nodes,
    root := Fin.ofNat' nodes.size self.root,
    filled := this
  })

def Graph.toHashMap (self : Graph) : Std.HashMap Nat Node :=
  self.nodes.foldl
      (fun (acc, i) n => (acc.insert i n, i + 1))
      (Std.HashMap.empty, 0)
    |>.fst

def Graph.toHashMapFin (self : Graph) : Std.HashMap (Fin self.nodes.size) Node :=
  self.nodes.foldl
      (fun (acc, i) n => (acc.insert (@Fin.ofNat' self.nodes.size self.filled i) n, i + 1))
      (Std.HashMap.empty, 0)
    |>.fst

def Graph.toHashSet (self : Graph) : Std.HashSet Node :=
  self.nodes.foldl (fun acc n => acc.insert n) Std.HashSet.empty

def Graph.satisfiable (self : Graph) (root : Fin self.nodes.size := self.root) (limit : Nat := self.nodes.size) : Bool :=
  match limit, self.nodes[root] with
    | 0, _ => false
    | _, .isFalse => false
    | _, .isTrue  => true
    | n + 1, node@(.node _ li hi) => match self.satisfiable (self.lowIndexOf node) n with
      | true  => true
      | false => self.satisfiable (self.highIndexOf node) n

/-- TODO: reset before assigning index.
Current version can't handle shared subtrees. -/
def Graph.compactNodes (_nodes: Array Node) : Graph :=
  -- topological sort
  default

/--
Checks if the node satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
def Graph.numberOfSatisfiedPathes (self : Graph)
    (root : Fin self.nodes.size := self.root)
    (counter : Std.HashMap (Fin self.nodes.size) Nat := Std.HashMap.empty)
    (limit : Nat := self.nodes.size)
    : Std.HashMap (Fin self.nodes.size) Nat × Nat :=
  if let some count := counter[root]? then (counter, count)
  else
    match limit, self.nodes[root] with
      | 0, _       => (counter, 0)
      | _, .isFalse => (counter, 0)
      | _, .isTrue  => (counter, 1)
      | n + 1, node =>
          let (c₁, k₁) := self.numberOfSatisfiedPathes (self.lowIndexOf node) counter n
          let (c₂, k₂) := self.numberOfSatisfiedPathes (self.highIndexOf node) c₁ n
          (c₂.insert root (k₁ + k₂), k₁ + k₂)

/--
Returns the number of satisfying assignments for the given node.
This is the number of paths. -/
def Graph.numSatisfies (self : Graph) : Nat :=
  self.numberOfSatisfiedPathes |>.snd
