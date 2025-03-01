import Std.Data.HashMap
import Std.Data.HashSet
import Common.TreeNode

open Std

/--
Implementation of node linking to two siblings in binary graph
It holds a boolean value and a unique identifier.
It is a derivation of `BEq`, `Hashable`, `Repr`, and `DecidableEq`. -/
inductive Node where
  | isFalse
  | isTrue
  | node (varId low high : Nat)
deriving BEq, Hashable, Repr

instance : Inhabited Node where
  default := .isFalse

def Node.toVarId (self : Node) : Nat := match self with
  | .isFalse => 0
  | .isTrue  => 0
  | .node varId _ _ => varId

def Node.newNode (varId low high: Nat) : Node :=
  .node varId low high

instance : ToString Node where
  toString (n : Node) : String := match n with
    | .isFalse => "#false"
    | .isTrue  => "#true"
    | .node varId 0 0 => s!"[v:{varId}=false]"
    | .node varId 0 1 => s!"[v:{varId}]"
    | .node varId 1 0 => s!"[v:-{varId}]"
    | .node varId 1 1 => s!"[v:{varId}=true]"
    | .node varId 0 h => s!"[v:{varId} l:false h:{h}]"
    | .node varId 1 h => s!"[v:{varId} l:true h:{h}]"
    | .node varId l 0 => s!"[v:{varId} l:{l} h:false]"
    | .node varId l 1 => s!"[v:{varId} l:{l} h:true]"
    | .node varId l h => s!"[v:{varId} l:{l} h:{h}]"

def Node.newConstant (value : Bool) : Node := match value with
  | false => .isFalse
  | true  => .isTrue

def Node.isConstant (self : Node) : Option Bool := match self with
  | .isFalse => some false
  | .isTrue  => some true
  | .node _ _ _ => none

def Node.ofTreeNode' (tree : TreeNode)
    (map : HashMap Nat Node := HashMap.empty) : HashMap Nat Node :=
  match tree with
    | TreeNode.isFalse => map.insert 0 .isFalse
    | TreeNode.isTrue  => map.insert 0 .isTrue
    | TreeNode.node varId low high id =>
      let map₁ := Node.ofTreeNode' low map
      let map₂ := Node.ofTreeNode' high map₁
      map₂.insert id (.node varId low.index high.index)

def Node.ofTreeNode (tree : TreeNode) : Array Node :=
  let mapping := Node.ofTreeNode' tree
  (Array.range mapping.size).map (mapping.getD · default)
