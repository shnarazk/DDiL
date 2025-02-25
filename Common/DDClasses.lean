import Std.Data.HashMap
import Std.Data.HashSet

open Std

/--
Implementation of node linking to two siblings in binary graph
It holds a boolean value and a unique identifier.
It is a derivation of `BEq`, `Hashable`, `Repr`, and `DecidableEq`.
-/
inductive Node where
  | asFalse
  | asTrue
  | node (id : Nat) (low high : Node)
deriving BEq, Hashable, Repr

instance : Inhabited Node where
  default := .asFalse

def Node.index (self : Node) : Nat := match self with
  | .asFalse => 0
  | .asTrue => 1
  | .node id _ _ => id

instance : ToString Node where
  toString (n : Node) : String := match n with
    | .asFalse => "leaf false"
    | .asTrue => "leaf true"
    | .node id low high => s!"node {id} {low.index} {high.index}"

def Node.newConstant (value : Bool) : Node := match value with
  | true => .asTrue
  | false => .asFalse

def Node.newVar (index : Nat) (low high : Node) : Node :=
  .node index low high

def Node.isConstant (self : Node) : Option Bool := match self with
  | .asFalse => some false
  | .asTrue => some true
  | .node _ _ _ => none

def Node.toHashSet (self : Node) (set : Std.HashSet Node := Std.HashSet.empty): Std.HashSet Node := match self with
  | .asFalse | .asTrue => set.insert self
  | .node _ low high => set.insert self |> low.toHashSet |> high.toHashSet

def Node.satisfiable (self : Node) : Bool := match self with
  | .asFalse => false
  | .asTrue => true
  | .node _ low high => match low.satisfiable with
    | true => true
    | false => high.satisfiable

/--
Checks if the node satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times.
-/
def linearCount (counter : Std.HashMap Node Nat) (n : Node) : Std.HashMap Node Nat × Nat :=
  if let some count := counter[n]? then (counter, count)
  else
    match n with
    | .asFalse => (counter, 0)
    | .asTrue => (counter, 1)
    | .node _ low high =>
        let (c₁, k₁) := linearCount counter low
        let (c₂, k₂) := linearCount c₁ high
        (c₂.insert n (k₁ + k₂), k₁ + k₂)

/--
Returns the number of satisfying assignments for the given node.
This is the number of paths.
-/
def Node.numSatisfies (self : Node) : Nat :=
  linearCount Std.HashMap.empty self |>.snd

/--
Interface for decision diagram built from `Node`.
-/
class DecisionDiagram (α : Type) [BEq α] where
  --  numberOfPaths : α → Nat
  allNodes : α → HashSet Node
  addNewConstant : α → Bool → α
  addNewVar (self : α) (index: Nat) (low high : Node) : α
--  index : α → Option Nat
--  buildIndexer : α → Std.HashMap α Nat × Std.HashMap Nat α

class ReducibleDecisionDiagram (α : Type) [BEq α] extends DecisionDiagram α where
  reduce : α → α
  apply : α → (Bool → Bool → Bool) → Bool → α
  compose : α → α → α
