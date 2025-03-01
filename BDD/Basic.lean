import Std
import Std.Data.HashMap
import Common.Node
import Common.Graph
import Common.DecisionDiagram

open Std

theorem nodes_contains_false (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 0 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))

theorem nodes_contains_true (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 1 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))

structure BDD extends Graph

instance : Inhabited BDD := ⟨{ toGraph := default }⟩

instance : ToString BDD where
  toString bdd := s!"[bdd {bdd.toGraph}]"

instance : BEq BDD where
  beq a b := a.toGraph == b.toGraph

instance : Coe Graph BDD where
  coe g := { toGraph := g }

def BDD.unusedId (self : BDD) : Nat := self.nodes.size

def BDD.mkConstant (self: BDD) (value : Bool) : Node × BDD :=
  (self.toGraph.constant value, self)

def BDD.addNewNode (self: BDD) (varId : Nat) (li hi : Nat) : Nat × BDD :=
  self.toGraph.addNewNode varId li hi
    |> fun (n, g) => (n, { self with toGraph := g })

instance : DecisionDiagram BDD where
  allNodes (self : BDD) := self.toGraph.nodes |> HashSet.ofArray
  addNewConstant := BDD.mkConstant
  addNewNode := BDD.addNewNode

example : (default : Node).toVarId = 0 := rfl

def lhn_le (a b : ((Nat × Nat) × Node)) : Bool :=
  a.fst.fst < b.fst.fst || (a.fst.fst == b.fst.fst && a.fst.snd < b.fst.snd)

/-- ddirの`for n in vlist[vi].iter().cloned()` に対応 -/
def aux_merge (indexer: HashMap Node Nat) (nodes: List Node) : (List ((Nat × Nat) × Node)) × HashMap Node Nat :=
  nodes.foldl
      (fun (acc, indexer) (node: Node) ↦ match node with
        | .isFalse | .isTrue => (acc, indexer)
        | .node _vi li hi =>
          if li == hi
          then (acc, indexer.insert node li)
          else (acc ++ [((li, hi), node)], indexer))
      ([], indexer)
    |> (fun (added, indexer) ↦ (added.mergeSort lhn_le, indexer))

def BBD.compact (_self : Array Node) (_start : Nat) : BDD := default

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def BDD.reduce₁ (self : BDD) (var_nodes: HashMap Nat (List Node)) : BDD :=
  let indexer : HashMap Node Nat := HashMap.empty
  let next_root : Nat := indexer.size
  var_nodes.toList.mergeSort (fun a b ↦ a.fst < b.fst)
    |>.reverse
    |>.foldl
        (fun (indexer, nodes) (v_list : (Nat × List Node)) ↦
          let (q, indexer) : List ((Nat × Nat) × Node) × HashMap Node Nat
            := aux_merge indexer v_list.snd
          -- use indexer, update nodes
          q.foldl
              (fun (indexer, nodes, oldKey) _ ↦ (indexer, nodes, oldKey))
              (indexer, nodes, (0,0))
            |> (fun (i, n, _) ↦ (i, n)))
        (indexer, self.toGraph.nodes)
    |>.snd
    |> (BBD.compact · next_root)

/-- Check the trivial cases. Otherwise pass to `reduce₁`. -/
def BDD.reduce (self : BDD) : BDD :=
  -- build a mapping from `varId` to `List node`
  let (_, all_false, all_true, var_nodes) := self.toGraph.nodes
      |>.toSubarray 2
      |>.foldl
        (fun (id, falses, trues, map) node => (
          id + 1,
          falses && (node == .isFalse),
          trues && (node == .isTrue),
          map.alter id (fun o => match o with
          | none => some [node]
          | some l => some (node :: l))))
      (0, true, true, (HashMap.empty : HashMap Nat (List Node)))
  match all_false, all_true with
    | true, _    => ↑{ (default : Graph) with root := Fin.ofNat' 2 0 }
    | _   , true => ↑{ (default : Graph) with root := Fin.ofNat' 2 1 }
    | _   , _    => self.reduce₁ var_nodes
