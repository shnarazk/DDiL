import Std.Data.HashMap
import Std.Data.HashSet

open Std

/--
Implementation of node linking to two siblings in binary graph
It holds a boolean value and a unique identifier.
It is a derivation of `BEq`, `Hashable`, `Repr`, and `DecidableEq`. -/
inductive Node where
  | isFalse
  | isTrue
  | node (varId : Nat) (low high : Node) (id : Nat)
deriving BEq, Hashable, Repr

instance : Inhabited Node where
  default := .isFalse

def Node.toVarId (self : Node) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 0
  | .node varId _ _ _ => varId

def Node.index (self : Node) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 1
  | .node _ _ _ id => id

instance : ToString Node where
  toString (n : Node) : String := match n with
    | .isFalse => "[false]"
    | .isTrue  => "[true]"
    | .node varId .isFalse .isFalse id => s!"[#{id} v:{varId}=false]"
    | .node varId .isFalse .isTrue  id => s!"[#{id} v:{varId}]"
    | .node varId .isTrue  .isFalse id => s!"[#{id} v:-{varId}]"
    | .node varId .isTrue  .isTrue  id => s!"[#{id} v:{varId}=true]"
    | .node varId .isFalse  high    id => s!"[#{id} v:{varId} l:false h:{high.toVarId}]"
    | .node varId .isTrue   high    id => s!"[#{id} v:{varId} l:true h:{high.toVarId}]"
    | .node varId  low     .isFalse id => s!"[#{id} v:{varId} l:{low.toVarId} h:false]"
    | .node varId  low     .isTrue  id => s!"[#{id} v:{varId} l:{low.toVarId} h:true]"
    | .node varId  low      high    id => s!"[#{id} v:{varId} l:{low.toVarId} h:{high.toVarId}]"

def Node.is_congruent (a b : Node) : Bool := match a, b with
  | .isFalse, .isFalse => true
  | .isTrue , .isTrue  => true
  | .node varId1 low1 high1 _, .node varId2 low2 high2 _ => varId1 = varId2 && low1.is_congruent low2 && high1.is_congruent high2
  | _, _ => false

def Node.newConstant (value : Bool) : Node := match value with
  | false => .isFalse
  | true  => .isTrue

def Node.newVar (varId : Nat) (low high : Node) (id : Nat) : Node :=
  .node varId low high id

def Node.isConstant (self : Node) : Option Bool := match self with
  | .isFalse => some false
  | .isTrue  => some true
  | .node _ _ _ _ => none

def Node.toHashMap (self : Node) (set : Std.HashMap Nat Node := Std.HashMap.empty)
    : Std.HashMap Nat Node := match self with
  | .isFalse => set.insert 0 self
  | .isTrue  => set.insert 1 self
  | .node _ low high _ => set.insert (self.index) self |> low.toHashMap |> high.toHashMap

def Node.toHashSet (self : Node) (set : Std.HashSet Node := Std.HashSet.empty): Std.HashSet Node := match self with
    | .isFalse | .isTrue => set.insert self
    | .node _ low high _ => set.insert self |> low.toHashSet |> high.toHashSet

def Node.satisfiable (self : Node) : Bool := match self with
  | .isFalse => false
  | .isTrue  => true
  | .node _ low high _ => match low.satisfiable with
    | true  => true
    | false => high.satisfiable

def Node.assignIndex (self : Node) (index : Nat := 2) : Node × Nat := match self with
  | .isFalse | .isTrue => (self, index)
  | .node varId low high _ =>
    let (l, i₁) := low.assignIndex index
    let (h, i₂) := high.assignIndex i₁
    (Node.newVar varId l h i₂, i₂ + 1)

/--
Checks if the node satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
def linearCount (counter : Std.HashMap Nat Nat) (n : Node) : Std.HashMap Nat Nat × Nat :=
  if let some count := counter[n.index]? then (counter, count)
  else
    match n with
      | .isFalse => (counter, 0)
      | .isTrue  => (counter, 1)
      | .node _ low high index =>
          let (c₁, k₁) := linearCount counter low
          let (c₂, k₂) := linearCount c₁ high
          (c₂.insert index (k₁ + k₂), k₁ + k₂)

/--
Returns the number of satisfying assignments for the given node.
This is the number of paths. -/
def Node.numSatisfies (self : Node) : Nat :=
  linearCount Std.HashMap.empty self |>.snd
