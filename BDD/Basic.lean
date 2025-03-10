import Std
import Std.Data.HashMap
import Common.Graph
import Common.GraphShape
import Common.DecisionDiagram

open Std

open Option in
def Option.unwrap {α : Type} [Inhabited α] (self : Option α) : α :=
  match self with | some a => a | none => default

-- #eval (some (3 : Nat)).unwrap

/-
theorem nodes_contains_false (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 0 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))

theorem nodes_contains_true (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 1 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))
-/

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

instance : GraphShape BDD where
  numberOfVars bdd := GraphShape.numberOfVars bdd.toGraph
  numberOfNodes _bdd := 0
  shapeOf bdd := GraphShape.shapeOf bdd.toGraph
  dumpAsDot bdd := GraphShape.dumpAsDot bdd.toGraph
  dumpAsPng bdd := GraphShape.dumpAsPng bdd.toGraph

instance : DecisionDiagram BDD where
  allNodes (self : BDD) :=
    self.toGraph.nodes.zipIdx |>.map (fun (n, i) => (i, n)) |> HashSet.ofArray
  numberOfPaths (_self : BDD) := 0

-- example : (default : Node).toVarId = 0 := rfl

namespace reducing

variable (g : Graph)

def order_to_scan (ia ib : Nat) : Bool := g.nodes[ia]! < g.nodes[ib]!

/-- Trim nodes that have the same li and hi refs. -/
def trim_nodes (updatedRef: HashMap Ref Ref) (targets: Array Ref) : Array Ref × HashMap Ref Ref :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.unwrap]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi
        then (acc, updatedRef.insert ref li)
        else (acc.push ref, updatedRef) )
    (#[], updatedRef)

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def reduce₁ (var_nodes: HashMap Nat (Array Ref)) : BDD :=
  -- mapping from old ref to new ref
  let updatedRef : HashMap Ref Ref := HashMap.empty
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes) (_, refs) ↦
        let (targets, updatedRef) : Array Ref × HashMap Ref Ref := trim_nodes g updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prevRef) nodeRef /- (key, node) -/ ↦
              let prev := nodes.getD prevRef.link.unwrap default
              let node := nodes[nodeRef.link.unwrap]!
              let node' := { node with
                              li := updatedRef.getD node.li node.li
                              hi := updatedRef.getD node.hi node.hi }
              if prev == node' then
                (updatedRef.insert nodeRef prevRef, nodes, prevRef)
              else
                (updatedRef, nodes.set! nodeRef.link.unwrap node', nodeRef)
            )
            (updatedRef, nodes, Ref.to nodes.size)
          |> (fun (updateRef, nodes, _) ↦ (updateRef, nodes)) )
      (updatedRef, g.nodes)
    |> (fun (_, (nodes : Array Node)) ↦ if 0 < nodes.size then
            Graph.fromNodes g.numVars nodes
          else
            default )
    |> (fun (g : Graph) ↦ {toGraph := g.compact})

end reducing

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
    | _   , _    => reducing.reduce₁ g var_nodes
