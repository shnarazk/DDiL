import Std
import Std.Data.HashMap
import Common.Graph
import Common.GraphShape
import Common.DecisionDiagram

open Std

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

-- def BDD.mkConstant (self: BDD) (value : Bool) : Node × BDD :=
--   (self.toGraph.constant value, self)

def BDD.addNode (self: BDD) (varId : Nat) (li hi : Ref) : BDD × Nat :=
  self.toGraph.addNode varId li hi
    |> fun (g, n) => ({self with toGraph := g}, n)

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

def order_to_scan (ia ib : Nat) : Bool :=
  if h : g.nodes[ia]! < g.nodes[ib]! then true else false

/-- ddirの`for n in vlist[vi].iter().cloned()` に対応 -/
def trim_nodes (updatedRef: HashMap Ref Ref) (targets: Array Nat) : Array Nat × HashMap Ref Ref :=
  targets.foldl
    (fun (acc, updatedRef) (id: Nat) ↦
      let node := g.nodes[id]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi
      then (acc, updatedRef.insert (Ref.to id) li)
      else (acc.push id, updatedRef)
    )
    (#[], updatedRef)

def BBD.compact (nodes : Array Node) (start : Nat) : BDD :=
  if h : 0 < nodes.size then
    have : NeZero nodes.size := by sorry
    -- FIXME: {nodes := nodes, root := Fin.ofNat' nodes.size start, filled := this}
    default
  else
    default

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def reduce₁ (g: Graph) (var_nodes: HashMap Nat (Array Nat)) : BDD :=
  -- mapping from old ref to new ref
  let updatedRef : HashMap Ref Ref := HashMap.empty
  let next_id := g.nodes.size
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
        (fun (next_id, updatedRef, nodes) (v_list : (Nat × List Node)) ↦
          let (q, updatedRef) : List ((Nat × Nat) × Node) × HashMap Ref Ref
            := trim_nodes updatedRef v_list.snd
          q.foldl
              (fun (next_id, updatedRef, nodes, oldKey) (key, node) ↦
                if oldKey == key then
                  (next_id, updatedRef.insert node next_id, nodes, key)
                else
                  -- FIXME: nothing done: update nodes using updatedRef
                  let next_id₁ := next_id + 1
                  match node with
                    | .isFalse | .isTrue => (next_id₁, updatedRef.insert node next_id₁, nodes.insert next_id₁ node, key)
                    | .node vi li hi =>
                      let newNode := Node.node vi li hi
                      let updatedRef := updatedRef.insert node next_id₁
                      let updatedRef := updatedRef.insert newNode next_id₁
                      (next_id₁, updatedRef, nodes.insert next_id₁ newNode, key)
                    )
              (next_id, updatedRef, nodes, (0,0))
            |> (fun (i, h, n, _) ↦ (i, h, n)) )
        (updatedRef.size, updatedRef, g.toHashMap)
    |> (fun (_, _, nodes) ↦
          nodes.toArray
            |>.insertionSort (·.fst < ·.fst)
            |>.map (·.snd))
    |> (fun (nodes : Array Node) ↦ if h : 0 < nodes.size
          then
            have : NeZero (nodes.size) := by sorry
            {nodes, root := @Fin.ofNat' nodes.size this next_id, filled := this }
          else default)
    |> (fun (g : Graph) ↦ ((↑g) : BDD))
    -- BBD.compact (nodes.toArray |>.insertionSort (·.fst < ·.fst) |>.map (·.snd)) next_id)

end reducing

/-- Check the trivial cases. Otherwise pass to `reduce₁`.
FIXME: don't take BDD. It shold be a `Array Node`.
-/
def BDD.reduce (self : BDD) : BDD :=
  let g := self.toGraph
  -- build a mapping from `varId` to `List node`
  let (all_false, all_true, var_nodes) := g.nodes.zipIdx.foldl
      (fun (falses, trues, mapping) (node, i) => (
        falses && (node.asBool == some false),
        trues && (node.asBool == some true),
        mapping.alter node.varId (fun list => match list with
          | none => some #[i]
          | some l => some (l.push i))))
    (true, true, (HashMap.empty : HashMap Nat (Array Nat)))
  match all_false, all_true with
    | true, _    => ↑{(default : Graph) with constant := false}
    | _   , true => ↑{(default : Graph) with constant := true}
    | _   , _    => reducing.reduce₁ g var_nodes
