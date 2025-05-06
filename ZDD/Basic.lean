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

abbrev ZDDKey := VarIndex × ZDD × ZDD
def ZDD.Key : Type := ZDDKey

/--
  Converts a ZDD to a human-readable string representation.

  Formats:
  - Nodes as `[ZDD: v t e]` where v is variable index, t and e are child nodes
  - Terminal 0 as "ZDD: 0"
  - Terminal 1 as "ZDD: 1"
-/
def toStringZDD (z : ZDD) := match z with
    | ZDD.node v t e => s!"[ZDD: {v} {toStringZDD t} {toStringZDD e}]"
    | ZDD.terminal0  => "⊥"
    | ZDD.terminal1  => "⊤"

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
  let mgr := (default : ZDD.manager)
  let (a, mgr) := makeNode mgr 0 ZDD.terminal1 ZDD.terminal0
  let (b, mgr) := makeNode mgr 1 ZDD.terminal1 ZDD.terminal0
  let (u, _mg) := zddUnion mgr a b
  IO.println s!"Union: {u} => {countPaths u}"
-/

/-
  ZDD.manager - Manages unique table to ensure canonicity of ZDD nodes.

  The unique table maps (variable, then-child, else-child) tuples to ZDD nodes,
  ensuring that equivalent nodes are shared for memory efficiency.
-/
structure ZDDManager where
  uniq : HashMap ZDDKey ZDD
deriving Inhabited

instance : ToString ZDDManager where
  toString m := List.map (toString · ++ "\n") m.uniq.toList |>String.join

def ZDDManager.get? (mgr : ZDDManager) (key : ZDDKey) : Option ZDD :=
  mgr.uniq.get? key

def ZDDManager.insert (mgr : ZDDManager) (key : ZDD.Key) (z : ZDD) : ZDDManager :=
  {mgr with uniq := mgr.uniq.insert key z}

def ZDD.manager : Type := ZDDManager

def ZDD.collectNodes (z : ZDD) (m : ZDDManager) : ZDDManager := match z with
  | node vi l h => if m.uniq.get? (vi, l, h) |>.isSome
    then m
    else l.collectNodes (m.insert (vi, l, h) z) |> (h.collectNodes ·)
  | _ => m

instance : Coe ZDD ZDDManager where
  coe z := ZDD.collectNodes z (default : ZDDManager)

-- #check (↑ ZDD.terminal0 : ZDDManager)
