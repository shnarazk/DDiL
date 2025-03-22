import Std.Data.HashMap
import Std.Data.HashSet
import Std.Internal.Parsec
import Std.Internal.Parsec.String
import Common.DecisionDiagram
import Common.GraphSerialize
import Common.GraphShape
import Common.LiftedBool
import Common.Parser

open Std

/--
Implementation of node linking to two siblings in binary graph
It holds a boolean value and a unique identifier.
It is a derivation of `BEq`, `Hashable`, `Repr`, and `DecidableEq`. -/
inductive TreeNode where
  | isFalse
  | isTrue
  | node (low high : TreeNode) (id : Nat)
deriving BEq, Hashable, Repr

instance : Inhabited TreeNode where
  default := .isFalse

def TreeNode.index (self : TreeNode) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 1
  | .node _ _ id => id

instance : ToString TreeNode where
  toString (n : TreeNode) : String := match n with
    | .isFalse => "#false"
    | .isTrue  => "#true"
    | .node .isFalse .isFalse id => s!"[#{id} false]"
    | .node .isFalse .isTrue  id => s!"[#{id} ⊥⊤]"
    | .node .isTrue  .isFalse id => s!"[#{id} ⊤⊥]"
    | .node .isTrue  .isTrue  id => s!"[#{id} true]"
    | .node .isFalse  high    id => s!"[#{id} l:false h:{high.index}]"
    | .node .isTrue   high    id => s!"[#{id} l:true h:{high.index}]"
    | .node  low     .isFalse id => s!"[#{id} l:{low.index} h:false]"
    | .node  low     .isTrue  id => s!"[#{id} l:{low.index} h:true]"
    | .node  low      high    id => s!"[#{id} l:{low.index} h:{high.index}]"

def TreeNode.depth (self : TreeNode) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 0
  | .node low high _ => 1 + max low.depth high.depth

def TreeNode.size (self : TreeNode) : Nat := match self with
  | .isFalse => 1
  | .isTrue  => 1
  | .node low high _ => 1 + low.size + high.size

def TreeNode.is_congruent (a b : TreeNode) : Bool := match a, b with
  | .isFalse, .isFalse => true
  | .isTrue , .isTrue  => true
  | .node low1 high1 _, .node low2 high2 _ => low1.is_congruent low2 && high1.is_congruent high2
  | _, _ => false

def TreeNode.newConstant (value : Bool) : TreeNode := match value with
  | false => .isFalse
  | true  => .isTrue

def TreeNode.newVar (low high : TreeNode) (id : Nat) : TreeNode :=
  .node low high id

def TreeNode.isConstant (self : TreeNode) : Option Bool := match self with
  | .isFalse    => some false
  | .isTrue     => some true
  | .node _ _ _ => none

def TreeNode.toHashMap (self : TreeNode) (set : Std.HashMap Nat TreeNode := Std.HashMap.empty)
    : Std.HashMap Nat TreeNode := match self with
  | .isFalse    => set.insert 0 self
  | .isTrue     => set.insert 1 self
  | .node l h _ => set.insert (self.index) self |> l.toHashMap |> h.toHashMap

def TreeNode.toHashSet (self : TreeNode) (set : Std.HashSet TreeNode := Std.HashSet.empty): Std.HashSet TreeNode := match self with
  | .isFalse | .isTrue => set.insert self
  | .node low high _   => set.insert self |> low.toHashSet |> high.toHashSet

def TreeNode.satisfiable (self : TreeNode) : Bool := match self with
  | .isFalse => false
  | .isTrue  => true
  | .node low high _ => match low.satisfiable with
    | true  => true
    | false => high.satisfiable

/-- TODO: reset before assigning index.
Current version can't handle shared subtrees. -/
def TreeNode.assignIndex (self : TreeNode) (index : Nat := 2) : TreeNode × Nat := match self with
  | .isFalse | .isTrue => (self, index)
  | .node low high _ =>
    let (l, i₁) := low.assignIndex (index + 1)
    let (h, i₂) := high.assignIndex i₁
    (TreeNode.newVar l h index, i₂)

namespace TreeNode_private
/--
Checks if the TreeNode satisfies all conditions.
Tree traversing approach isn't efficient because it visits subtrees many times. -/
def count (counter : Std.HashMap Nat Nat) (n : TreeNode) : Std.HashMap Nat Nat × Nat :=
  if let some count := counter[n.index]? then (counter, count)
  else
    match n with
    | .isFalse => (counter, 0)
    | .isTrue  => (counter, 1)
    | .node low high index =>
        let (c₁, k₁) := count counter low
        let (c₂, k₂) := count c₁ high
        (c₂.insert index (k₁ + k₂), k₁ + k₂)

end TreeNode_private

/--
Returns the number of satisfying assignments for the given TreeNode.
This is the number of paths. -/
def TreeNode.numSatisfies (self : TreeNode) : Nat :=
  TreeNode_private.count Std.HashMap.empty self |>.snd

namespace TreeNode_parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open ParserLib

def parse_comment : Parser String := do
  let _ ← pchar '"'
  let s ← many (satisfy (· != '"'))
  let _ ← pchar '"'
  return (s.toList.map toString |>String.join)

def parse_false : Parser TreeNode := do
  let _ ← pchar 'F'
  return TreeNode.isFalse

def parse_true : Parser TreeNode := do
  let _ ← pchar 'T'
  return TreeNode.isTrue

mutual

partial def parse_block : Parser TreeNode := do
  let _ ← pchar '{' <* delimiter?
  let f ← (orElse (parse_comment *> delimiter? *> parse_tf) (fun _ ↦ parse_tf)) <* delimiter
  -- let f ← parse_tf <* delimiter
  let t ← parse_tf <* delimiter?
  let _ ← pchar '}'
  return TreeNode.newVar f t 0

partial def parse_tf : Parser TreeNode :=
  parse_false <|> parse_true <|> parse_block

end -- of mutual

-- #eval ParserLib.parse parse_tf "{"0" F F}"

end TreeNode_parser

def TreeNode.fromString (input : String) : TreeNode :=
  match ParserLib.parse TreeNode_parser.parse_tf input with
    |some tree => tree.assignIndex.fst
    |none => TreeNode.isFalse

-- #eval TreeNode.fromString "F"
-- #eval TreeNode.fromfString "T"
-- #eval TreeNode.fromfString "{1 T F}"

instance : GraphShape TreeNode where
  numberOfVars := (·.depth)
  numberOfNodes := (·.size)

instance : GraphSerialize TreeNode where
  dumpAsDot _ filename := do return filename
  dumpAsPng := fun _ filename => do return filename

instance : DecisionDiagram TreeNode where
  numberOfSatisfyingPaths (t : TreeNode) := t.numSatisfies
  apply (_f : LiftedBool.BinaryFunction) (t _ : TreeNode) : TreeNode := t
  compose (self _other : TreeNode) (_varId : Nat) : TreeNode := self
  isCongruent (self other : TreeNode) : Bool := self.is_congruent other
  contains (_self : TreeNode) (_exp : List Int) : Bool := true
