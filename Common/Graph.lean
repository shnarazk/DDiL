import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet
import Common.Node
import Common.Debug
import Common.TreeNode

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

instance : Inhabited (Graph × Nat) where
  default := (default, 0)

instance : ToString Graph where
  toString g := s!"[graph {g.nodes.size} nodes]"

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

protected def Graph.is_congruent₁ (limit : Nat) (g₁ g₂ : Graph)
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

def Graph.reachableNodes (self : Graph) (start : Nat := self.root)
    (map : HashMap Nat Node := HashMap.empty)
    (limit : Nat := self.nodes.size)
    : HashMap Nat Node :=
    match limit, map.contains start with
      | 0, _ => HashMap.empty
      | _, true => map
      | n + 1, false =>  match self.nodes[start]? with
        | none => HashMap.empty
        | some .isFalse => map.insert 0 .isFalse
        | some .isTrue => map.insert 1 .isTrue
        | some node@(.node _ li hi) =>
          map.insert start node
          |> (self.reachableNodes li · n)
          |> (self.reachableNodes hi · n)

def Graph.toHashMap (self : Graph) : Std.HashMap Nat Node :=
  self.reachableNodes.fold (fun acc n node => acc.insert n node) Std.HashMap.empty

def Graph.toHashMapFin (self : Graph) : Std.HashMap (Fin self.nodes.size) Node :=
  self.reachableNodes.fold
    (fun acc n node => acc.insert (@Fin.ofNat' self.nodes.size self.filled n) node)
    Std.HashMap.empty

def Graph.toHashSet (self : Graph) : Std.HashSet Node :=
  self.reachableNodes.fold (fun acc _ node => acc.insert node) Std.HashSet.empty

def Graph.satisfiable (self : Graph) (root : Fin self.nodes.size := self.root) (limit : Nat := self.nodes.size) : Bool :=
  match limit, self.nodes[root] with
    | 0, _ => false
    | _, .isFalse => false
    | _, .isTrue  => true
    | n + 1, node@(.node _ li hi) => match self.satisfiable (self.lowIndexOf node) n with
      | true  => true
      | false => self.satisfiable (self.highIndexOf node) n

/-- FIXME: to proove this, we need mathlib 😔 -/
theorem size_of_hash_with_zero {α : Type} (l : HashMap Nat α) : l.contains 0 → NeZero l.size := by
  intro h
  have h₁ : 0 ∈ l := by exact h
  have size_erase : (l.erase 0).size = if 0 ∈ l then l.size - 1 else l.size := by
    exact HashMap.size_erase
  simp [h₁] at size_erase
  have : (l.erase 0).size + 1 = l.size := by sorry
  have size_ge_zero : ∀ h : HashMap Nat α, 0 ≤ h.size := by exact fun h ↦ Nat.zero_le h.size
  rcases size_ge_zero (l.erase 0) with l'_size
  have : 0 ≤ l.size - 1 := by exact Nat.zero_le (l.size - 1)
  have : 0 ≠ l.size := by sorry
  exact { out := id (Ne.symm this) }

/-- TODO: reset before assigning index.
Current version can't handle shared subtrees. -/
def Graph.compactNodes (self: Graph) : Graph :=
  let nodeMap : HashMap Nat Node := self.reachableNodes.filter (fun _ node => node.isConstant.isNone)
  -- let keys : List Nat := nodeMap.keys
  let indices : HashMap Nat Nat := [0, 1] ++ nodeMap.keys
    |>.zipIdx
    |>.map (fun (n : Nat × Nat) ↦ (n.snd, n.fst))
    |> HashMap.ofList
  let nodes : Array Node := Array.range indices.size
    |>.map
      (fun (i : Nat) => match i with
     | 0 => Node.isFalse
     | 1 => Node.isTrue
     | _ => match nodeMap[i]! with
       | Node.node vi li hi => Node.node vi indices[li]! indices[hi]!
       | _ => Node.isFalse)
  have indices_has_zero : indices.contains 0 := by sorry
  have indices_filled : NeZero indices.size := by
    exact size_of_hash_with_zero indices indices_has_zero
  have nodes_filled : NeZero nodes.size := by sorry
  { nodes := nodes,
    root := Fin.ofNat' nodes.size self.root.val,
    filled := nodes_filled }

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
      | 0, _        => (counter, 0)
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

def Graph.dumpAsDot (self : Graph) (path : String) : IO Unit := do
  let buffer := "digraph regexp {
    fontname=\"Helvetica,Arial,sans-serif\"
    node [fontname=\"Helvetica,Arial,sans-serif\"]
    edge [fontname=\"Helvetica,Arial,sans-serif\", color=blue]
  "
  let nodes := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦ match node, i with
        | _, 0 => "  0 [style=filled, fillcolor=\"gray80\",label=\"false\",shape=\"box\"];\n"
        | _, 1 => "  1 [style=filled, fillcolor=\"gray95\",label=\"true\",shape=\"box\"];\n"
        | .node vi _ _, i => s!"  {i} [label=\"{vi}\"];\n"
        | _, _ => ""
      )
    |> String.join
  let edges := self.nodes.toList.zipIdx.map
      (fun (node, i) ↦ match node with
        | .isFalse => ""
        | .isTrue => ""
        | .node _ li hi => if li = hi
            then
              s!" {i} -> {li} [color=black,penwidth=2];\n"
            else
              s!" {i} -> {li} [color=red,style=\"dotted\"];\n" ++
              s!" {i} -> {hi} [color=blue];\n" )
    |> String.join
  IO.FS.writeFile path (buffer ++ "\n" ++ nodes ++ "\n" ++ edges ++ "\n}\n")

def Graph.ofTreeNode (tree : TreeNode) : Graph :=
  let nodes := Node.ofTreeNode tree
  if h: 0 < nodes.size then
    have : 0 ≠ nodes.size := by
      exact Ne.symm (Nat.not_eq_zero_of_lt h)
    have : NeZero nodes.size := by
      exact { out := id (Ne.symm this) }
    {
      nodes := nodes,
      root := @Fin.ofNat' nodes.size this tree.index,
      filled := this
    }
  else
    default

instance : Coe TreeNode Graph where
  coe t := Graph.ofTreeNode t.assignIndex.fst
