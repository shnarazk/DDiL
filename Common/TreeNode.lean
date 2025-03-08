import Std.Data.HashMap
import Std.Data.HashSet
import Std.Internal.Parsec
import Std.Internal.Parsec.String
import Common.Parser

open Std

/--
Implementation of node linking to two siblings in binary graph
It holds a boolean value and a unique identifier.
It is a derivation of `BEq`, `Hashable`, `Repr`, and `DecidableEq`. -/
inductive TreeNode where
  | isFalse
  | isTrue
  | node (varId : Nat) (low high : TreeNode) (id : Nat)
deriving BEq, Hashable, Repr

instance : Inhabited TreeNode where
  default := .isFalse

def TreeNode.toVarId (self : TreeNode) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 0
  | .node varId _ _ _ => varId

def TreeNode.index (self : TreeNode) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 1
  | .node _ _ _ id => id

instance : ToString TreeNode where
  toString (n : TreeNode) : String := match n with
    | .isFalse => "#false"
    | .isTrue  => "#true"
    | .node varId .isFalse .isFalse id => s!"[#{id} v:{varId}=false]"
    | .node varId .isFalse .isTrue  id => s!"[#{id} v:{varId}]"
    | .node varId .isTrue  .isFalse id => s!"[#{id} v:-{varId}]"
    | .node varId .isTrue  .isTrue  id => s!"[#{id} v:{varId}=true]"
    | .node varId .isFalse  high    id => s!"[#{id} v:{varId} l:false h:{high.toVarId}]"
    | .node varId .isTrue   high    id => s!"[#{id} v:{varId} l:true h:{high.toVarId}]"
    | .node varId  low     .isFalse id => s!"[#{id} v:{varId} l:{low.toVarId} h:false]"
    | .node varId  low     .isTrue  id => s!"[#{id} v:{varId} l:{low.toVarId} h:true]"
    | .node varId  low      high    id => s!"[#{id} v:{varId} l:{low.toVarId} h:{high.toVarId}]"

def TreeNode.is_congruent (a b : TreeNode) : Bool := match a, b with
  | .isFalse, .isFalse => true
  | .isTrue , .isTrue  => true
  | .node varId1 low1 high1 _, .node varId2 low2 high2 _ => varId1 = varId2 && low1.is_congruent low2 && high1.is_congruent high2
  | _, _ => false

def TreeNode.newConstant (value : Bool) : TreeNode := match value with
  | false => .isFalse
  | true  => .isTrue

def TreeNode.newVar (varId : Nat) (low high : TreeNode) (id : Nat) : TreeNode :=
  .node varId low high id

def TreeNode.isConstant (self : TreeNode) : Option Bool := match self with
  | .isFalse => some false
  | .isTrue  => some true
  | .node _ _ _ _ => none

def TreeNode.toHashMap (self : TreeNode) (set : Std.HashMap Nat TreeNode := Std.HashMap.empty)
    : Std.HashMap Nat TreeNode := match self with
  | .isFalse => set.insert 0 self
  | .isTrue  => set.insert 1 self
  | .node _ low high _ => set.insert (self.index) self |> low.toHashMap |> high.toHashMap

def TreeNode.toHashSet (self : TreeNode) (set : Std.HashSet TreeNode := Std.HashSet.empty): Std.HashSet TreeNode := match self with
    | .isFalse | .isTrue => set.insert self
    | .node _ low high _ => set.insert self |> low.toHashSet |> high.toHashSet

def TreeNode.satisfiable (self : TreeNode) : Bool := match self with
  | .isFalse => false
  | .isTrue  => true
  | .node _ low high _ => match low.satisfiable with
    | true  => true
    | false => high.satisfiable

/-- TODO: reset before assigning index.
Current version can't handle shared subtrees. -/
def TreeNode.assignIndex (self : TreeNode) (index : Nat := 2) : TreeNode × Nat := match self with
  | .isFalse | .isTrue => (self, index)
  | .node varId low high _ =>
    let (l, i₁) := low.assignIndex (index + 1)
    let (h, i₂) := high.assignIndex i₁
    (TreeNode.newVar varId l h index, i₂)

/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
def linearCount (counter : Std.HashMap Nat Nat) (n : TreeNode) : Std.HashMap Nat Nat × Nat :=
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
Returns the number of satisfying assignments for the given TreeNode.
This is the number of paths. -/
def TreeNode.numSatisfies (self : TreeNode) : Nat :=
  linearCount Std.HashMap.empty self |>.snd

namespace parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open ParserLib

def parse_false : Parser TreeNode := do
  let _ ← pchar 'F'
  return TreeNode.isFalse

def parse_true : Parser TreeNode := do
  let _ ← pchar 'T'
  return TreeNode.isTrue

mutual

partial def parse_block : Parser TreeNode := do
  let _ ← pchar '{' <* delimiter?
  let vi ← number <* delimiter
  let f ← parse_tf <* delimiter
  let t ← parse_tf <* delimiter?
  let _ ← pchar '}'
  return TreeNode.newVar vi f t 0

partial def parse_tf : Parser TreeNode :=
  parse_false <|> parse_true <|> parse_block

end

-- #eval ParserLib.parse parse_tf "{0 F F}"

end parser

def TreeNode.ofString (input : String) : TreeNode :=
  match ParserLib.parse parser.parse_tf input with
    |some tree => tree.assignIndex.fst
    |none => TreeNode.isFalse

-- #eval TreeNode.ofString "F"
-- #eval TreeNode.ofString "T"
-- #eval TreeNode.ofString "{1 T F}"
