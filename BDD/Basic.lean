import Std
import Std.Data.HashMap
import Common.Graph
import Common.GraphShape
import Common.DecisionDiagram

open Std

structure BDD extends Graph

instance : Inhabited BDD := ⟨{toGraph := default}⟩

instance : ToString BDD where
  toString bdd := s!"[bdd {bdd.toGraph}]"

instance : BEq BDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe Graph BDD where
  coe g := { toGraph := g }

def BDD.unusedId (self : BDD) : Nat := self.nodes.size

def BDD.addNode (self: BDD) (node : Node) : BDD × Nat :=
  self.toGraph.addNode node
    |> fun (g, n) => ({self with toGraph := g}, n)

def BDD.addNode' (self: BDD) (varId : Nat) (li hi : Ref) : BDD × Nat :=
  self.addNode {varId, li, hi}

-- example : (default : Node).toVarId = 0 := rfl

namespace BDD_private

variable (g : Graph)

def path_distance (a b : Ref) : Nat :=
  match a.link, b.link with
  | none,   none   => 0
  | none,   some _ => 0
  | some i, none   => 2 ^ (g.numVars - g.nodes[i]!.varId)
  | some i, some j => 2 ^ (g.nodes[j]!.varId - g.nodes[i]!.varId).pred

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
partial def linearCount (g : Graph) (counter : Std.HashMap Ref Nat) (r : Ref) (depth : Nat) : Std.HashMap Ref Nat × Nat :=
  match r.link with
  | none => (counter, if r.grounded then 1 else 0)
  | some i =>
    if let some count := counter[r]? then (counter, count)
    else
      let node := g.nodes[i]!
      let (counter, a') := linearCount g counter node.li depth.pred
      let a := (path_distance g r node.li) * a'
      let (counter, b') := linearCount g counter node.hi depth.pred
      let b := (path_distance g r node.hi) * b'
      (counter.insert r (a + b), (a + b))

def order_to_scan (ia ib : Nat) : Bool := g.nodes[ia]! < g.nodes[ib]!

/-- Trim nodes that have the same li and hi refs. -/
def trim_nodes (updatedRef: HashMap Ref Ref) (targets: Array Ref) : Array Ref × HashMap Ref Ref :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi
        then (acc, updatedRef.insert ref li)
        else (acc.push ref, updatedRef) )
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

variable (bdd : BDD)

def apply (_f : Bool → Bool → Bool) (_unit : Bool) : BDD :=
  bdd

def compose (_other : BDD) (_varIndex : Nat) : BDD :=
  bdd

end BDD_private

/-- Check the trivial cases. Otherwise pass to `reduce₁`. -/
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
    | _   , _    => BDD_private.reduce g var_nodes

def BDD.apply (self : BDD) (f : Bool → Bool → Bool) (unit : Bool) : BDD :=
  BDD_private.apply self f unit

def BDD.compose (self : BDD) (other : BDD) (varIndex : Nat) : BDD :=
  BDD_private.compose self other varIndex

instance : GraphShape BDD where
  numberOfVars bdd := GraphShape.numberOfVars bdd.toGraph
  numberOfNodes _bdd := 0
  shapeOf bdd := GraphShape.shapeOf bdd.toGraph
  dumpAsDot bdd := GraphShape.dumpAsDot bdd.toGraph
  dumpAsPng bdd := GraphShape.dumpAsPng bdd.toGraph
--

def BDD.numSatisfies (self : BDD) : Nat :=
  if self.nodes.isEmpty then
    2 ^ self.numVars
  else
    let nodes := self.toGraph.nodes
    BDD_private.linearCount
        self.toGraph
        Std.HashMap.empty
        (Ref.to nodes.size.pred)
        self.numVars
      |>.snd

instance : DecisionDiagram BDD where
  numberOfSatisfyingPaths b := b.numSatisfies
  apply := BDD.apply
  compose := BDD.compose
