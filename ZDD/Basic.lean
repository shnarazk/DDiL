import Std.Data.HashMap

open Std

abbrev VarIndex := Nat
/--
  ZDD (Zero-suppressed Decision Diagram) - A data structure for efficiently representing and
  manipulating sets of combinations.

  Core components:
  - `node`: Internal node with variable index, then-child (1-edge), and else-child (0-edge)
  - `terminal0`: Terminal node representing empty set (⊥)
  - `terminal1`: Terminal node representing the set containing only empty set (⊤)
-/
inductive ZDD
| node : VarIndex → ZDD → ZDD → ZDD
| terminal0 : ZDD
| terminal1 : ZDD
deriving BEq, Hashable, Repr

instance : Inhabited ZDD where
  default := ZDD.terminal0

/--
  Converts a ZDD to a human-readable string representation.

  Formats:
  - Nodes as `[ZDD: v t e]` where v is variable index, t and e are child nodes
  - Terminal 0 as "ZDD: 0"
  - Terminal 1 as "ZDD: 1"
-/
def toStringZDD (z : ZDD) := match z with
    | ZDD.node v t e => s!"[ZDD: {v} {toStringZDD t} {toStringZDD e}]"
    | ZDD.terminal0  => "ZDD: 0"
    | ZDD.terminal1  => "ZDD: 1"

/--
  Implements ToString typeclass for ZDD using the toStringZDD function
-/
instance : ToString ZDD where
  toString := toStringZDD


/-
  Main function demonstrating basic ZDD operations.

  Creates two simple ZDDs:
  - a: ZDD for the set {0}
  - b: ZDD for the set {1}

  Then computes and prints their union, which represents the family {0}, {1}.
-/
/-
def main : IO Unit :=
  let mgr := (default : ZDDManager)
  let (a, mgr) := make_node mgr 0 ZDD.terminal1 ZDD.terminal0
  let (b, mgr) := make_node mgr 1 ZDD.terminal1 ZDD.terminal0
  let (u, _mg) := zdd_union mgr a b
  IO.println s!"Union: {u} => {countPaths u}"
-/
