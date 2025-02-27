import Std
import Std.Data.HashMap
import Common.Node
import Common.DecisionDiagram

open Std

theorem nodes_contains_false (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 0 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))

theorem nodes_contains_true (nodes : HashMap Nat Node) : (nodes.insertMany [(0, .isFalse), (1, .isTrue)]).contains 1 := by
  rw [HashMap.contains_insertMany_list]
  exact Eq.symm ((fun {a b} ↦ Bool.iff_or_self.mpr) (congrFun rfl))

structure BDD where
  tree : Node
  nodes : HashMap Nat Node := HashMap.empty |>.insert 0 Node.isFalse |>.insert 1 Node.isTrue
  has_false : nodes.contains 0 := by trivial
  has_true  : nodes.contains 1 := by trivial

instance : Inhabited BDD where
  default :=
    let base := HashMap.empty |>.insert 0 Node.isFalse |>.insert 1 Node.isTrue
    { tree := Node.isFalse,
      nodes := base,
      has_false := by rw [HashMap.contains_insert] ; simp,
      has_true  := by rw [HashMap.contains_insert] ; simp
    }

instance : BEq BDD where
  beq (self other : BDD) := Node.is_congruent self.tree other.tree

def BDD.of (root : Node) : BDD :=
  let nodes : HashMap Nat Node := root.assignIndex.fst.toHashMap
  let nodes₁ := nodes.insertMany [(0, Node.isFalse), (1, Node.isTrue)]
  { tree := root,
    nodes := nodes₁,
    has_false := nodes_contains_false nodes,
    has_true  := nodes_contains_true nodes }

def BDD.unusedId (self : BDD) : Nat := self.nodes.size

def BDD.mkConstant (self: BDD) (value : Bool) : Node × BDD :=
  (if value then self.nodes[1]'self.has_true else self.nodes[0]'self.has_false, self)

def BDD.mkNewVar (self: BDD) (varId : Nat) (low high : Node) : Node × BDD :=
  let k := self.unusedId
  let n := Node.newVar varId low high k
  let nodes := self.nodes
  let nodes₁ := nodes.insert k n
  (n, {self with
    nodes := nodes₁,
    has_false := by
      rw [HashMap.contains_insert]
      exact Lean.Grind.Bool.or_eq_of_eq_true_right self.has_false
    has_true := by
      rw [HashMap.contains_insert]
      exact Lean.Grind.Bool.or_eq_of_eq_true_right self.has_true
  })

instance : DecisionDiagram BDD where
  allNodes (self : BDD) := self.nodes |>.values |> HashSet.ofList
  addNewConstant := BDD.mkConstant
  addNewVar := BDD.mkNewVar

example : (default : Node).toVarId = 0 := rfl

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def BDD.reduce₁ (self : BDD) (_var_nodes: HashMap Nat (List Node)) : BDD :=
  self

/-- Check the trivial cases. Otherwise pass to `reduce₁`. -/
def BDD.reduce (self : BDD) : BDD :=
  let _root := self.tree
  -- build a mapping from `varId` to `List node`
  let (all_false, all_true, var_nodes) := self.nodes.fold
      (fun (falses, trues, map) id node => (
          falses && (node == .isFalse),
          trues && (node == .isTrue),
          map.alter id (fun o => match o with
          | none => some [node]
          | some l => some (node :: l))))
      (true, true, (HashMap.empty : HashMap Nat (List Node)))
  match all_false, all_true with
    | true, _    => (default : BDD)
    | _   , true => { (default : BDD) with tree := .isTrue }
    | _   , _    => self.reduce₁ var_nodes
