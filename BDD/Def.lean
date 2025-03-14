import Std.Data.HashMap
import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Graph.Def

open Std

structure BDD extends Graph

instance : Inhabited BDD := ⟨{toGraph := default}⟩

instance : ToString BDD where
  toString bdd := s!"[bdd {bdd.toGraph}]"

instance : BEq BDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe BDD Graph where
  coe b := b.toGraph

instance : Coe BDD (Array Node) where
  coe b := b.toGraph.nodes

def BDD.unusedId (self : BDD) : Nat := self.nodes.size

def BDD.addNode (self: BDD) (node : Node) : BDD × Nat :=
  self.toGraph.addNode node
    |> fun (g, n) => ({self with toGraph := g}, n)

def BDD.addNode' (self: BDD) (varId : Nat) (li hi : Ref) : BDD × Nat :=
  self.addNode {varId, li, hi}

namespace BDD

variable (g : Graph)

private def path_distance (a b : Ref) : Nat :=
  match a.link, b.link with
  | none,   none   => 0
  | none,   some _ => 0
  | some i, none   => 2 ^ (g.numVars - g.nodes[i]!.varId)
  | some i, some j => 2 ^ (g.nodes[j]!.varId - g.nodes[i]!.varId).pred

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
partial def countPaths (g : Graph) (counter : Std.HashMap Ref Nat) (r : Ref) : Std.HashMap Ref Nat × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a') := countPaths g counter node.li
      let a := (path_distance g r node.li) * a'
      let (counter, b') := countPaths g counter node.hi
      let b := (path_distance g r node.hi) * b'
      (counter.insert r (a + b), (a + b))

private def order_to_scan (ia ib : Nat) : Bool := g.nodes[ia]! < g.nodes[ib]!

/-- Trim nodes that have the same li and hi refs. -/
def trim_nodes (updatedRef: HashMap Ref Ref) (targets: Array Ref) : Array Ref × HashMap Ref Ref :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi then (acc, updatedRef.insert ref li) else (acc.push ref, updatedRef) )
    (#[], updatedRef)

def merge_nodes (updatedRef: HashMap Ref Ref) (nodes: Array Node) (prevRef : Ref) (nodeRef : Ref)
    : HashMap Ref Ref × Array Node × Ref :=
  let prev := nodes.getD (prevRef.link.getD 0) default
  let node : Node := nodes[nodeRef.link.getD 0]!
  let node' : Node := { node with
    li := updatedRef.getD node.li node.li
    hi := updatedRef.getD node.hi node.hi }
  if prev == node' then
    (updatedRef.insert nodeRef prevRef, nodes, prevRef)
  else
    (updatedRef, nodes.set! (nodeRef.link.getD 0) node', nodeRef)

def append_nodes (self other : Array Node) (offset : Nat := self.size) : Array Node :=
  self.append <| other.map (fun n ↦ {n with li := n.li + offset, hi := n.hi + offset})

-- #eval append_nodes #[(default : Node), default] #[{(default : Node) with li := Ref.to 0}]

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def reduce (var_nodes: HashMap Nat (Array Ref)) : BDD :=
  -- mapping from old ref to new ref
  let updatedRef : HashMap Ref Ref := HashMap.empty
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes) (_, refs) ↦
        let (targets, updatedRef) : Array Ref × HashMap Ref Ref := trim_nodes g updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prev) next ↦ merge_nodes updatedRef nodes prev next)
            (updatedRef, nodes, Ref.to nodes.size)
          |> (fun (updateRef, nodes, _) ↦ (updateRef, nodes)) )
      (updatedRef, g.nodes)
    |> (fun (_, (nodes : Array Node)) ↦ if 0 < nodes.size then
            Graph.fromNodes g.numVars nodes
          else
            default )
    |> (fun (g : Graph) ↦ {toGraph := g.compact})

def compose (a _b : BDD) (_varIndex : Nat) : BDD :=
  a

partial def apply_aux (f : MergeFunction) (r₁ r₂ : Ref) (nodes : Array Node)
    (merged : HashMap (Ref × Ref) Ref)
    : (Ref × (Array Node) × (HashMap (Ref × Ref) Ref)) :=
  if let some r := merged.get? (r₁, r₂) then
    (r, nodes, merged)
  else if let some b := f.apply r₁.asBool r₂.asBool then
    let r := Ref.bool b
    (r, nodes, merged.insert (r₁, r₂) r)
  else match r₁.link, r₂.link with
    | none,   none   =>
        let r := Ref.bool <| (↑f : Bool → Bool → Bool) r₁.grounded r₂.grounded
        (r, nodes, merged.insert (r₁, r₂) r)
    | none,   some _ => (r₂, nodes, merged.insert (r₁, r₂) r₂)
    | some _, none   => (r₁, nodes, merged.insert (r₁, r₂) r₁)
    | some a, some b =>
      let node1 : Node := nodes[a]!
      let node2 : Node := nodes[b]!
      let vi : Nat := Nat.min node1.varId node2.varId
      let (l1, h1) := if vi == node1.varId then (node1.li, node1.hi) else (r₁, r₁)
      let (l2, h2) := if vi == node2.varId then (node2.li, node2.hi) else (r₂, r₂)
      let (l, nodes, merged) := apply_aux f l1 l2 nodes merged
      let (h, nodes, merged) := apply_aux f h1 h2 nodes merged
      let r := Ref.to nodes.size
      (r, nodes.push {varId := vi, li := l, hi := h}, merged.insert (r₁, r₂) r)

end BDD

/-- Check the trivial cases. Otherwise pass to `reduce`. -/
def Graph.toBDD (g : Graph) : BDD :=
  -- build a mapping from `varId` to `List node`
  let (all_false, all_true, var_nodes) := g.nodes.zipIdx.foldl
    (fun (falses, trues, mapping) (node, i) =>
     ( falses && (node.asBool == some false),
       trues && (node.asBool == some true),
       mapping.alter
         node.varId
         (fun list => match list with
           | none => some #[Ref.to i]
           | some l => some (l.push (Ref.to i)) )))
    (true, true, (HashMap.empty : HashMap Nat (Array Ref)))
  match all_false, all_true with
    | true, _    => ↑{(default : Graph) with constant := false}
    | _   , true => ↑{(default : Graph) with constant := true}
    | _   , _    => BDD.reduce g var_nodes

instance : GraphShape BDD where
  numberOfVars self := GraphShape.numberOfVars (↑self : Graph)
  numberOfNodes self := GraphShape.numberOfNodes (↑self : Graph)
  shapeOf self := GraphShape.shapeOf (↑self : Graph)
  dumpAsDot self := GraphShape.dumpAsDot (↑self : Graph)
  dumpAsPng self := GraphShape.dumpAsPng (↑self : Graph)

def BDD.numSatisfies (self : BDD) : Nat :=
  if self.nodes.isEmpty then
    2 ^ self.numVars
  else
    BDD.countPaths ↑self Std.HashMap.empty (Ref.to self.toGraph.nodes.size.pred) |>.snd

def BDD.apply (operator : MergeFunction) (self other : BDD) : BDD :=
  let r1 := Ref.to self.toGraph.nodes.size.pred
  let all_nodes : Array Node := BDD.append_nodes ↑self ↑other
  let r2 := Ref.to all_nodes.size.pred
  BDD.apply_aux operator r1 r2 all_nodes HashMap.empty
    |> (fun (_, (nodes : Array Node), _) ↦ if nodes.isEmpty then
              default
            else
              Graph.fromNodes (Nat.max self.numVars other.numVars) nodes )
    |> (·.compact.toBDD)

instance : DecisionDiagram BDD where
  numberOfSatisfyingPaths b := b.numSatisfies
  apply := BDD.apply
  compose := BDD.compose
