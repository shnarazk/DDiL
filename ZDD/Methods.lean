import Std.Data.HashMap
import ZDD.Basic

open Std

/--
  ZDDManager - Manages unique table to ensure canonicity of ZDD nodes.

  The unique table maps (variable, then-child, else-child) tuples to ZDD nodes,
  ensuring that equivalent nodes are shared for memory efficiency.
-/
structure ZDDManager where
  uniq : HashMap (Nat × ZDD × ZDD) ZDD
deriving Inhabited

/--
  Creates a new ZDD node with zero-suppression rules applied.

  Zero-suppression rules:
  1. If then-child is terminal0, return else-child (core zero-suppression rule)
  2. If then-child equals else-child, return either (redundant node elimination)
  3. Otherwise, create or reuse a unique node via the unique table

  Parameters:
  - mgr: The ZDD manager containing the unique table
  - v: Variable index
  - t: Then-child (1-edge)
  - e: Else-child (0-edge)

  Returns:
  - A tuple of (resulting ZDD node, updated manager)
-/
def make_node (mgr : ZDDManager) (v : Nat) (t e : ZDD) : ZDD × ZDDManager :=
  if t == ZDD.terminal0 then
    (e, mgr)
  else if t == e then
    (t, mgr)
  else
    let key := (v, t, e)
    match mgr.uniq.get? key with
    | some n => (n, mgr)
    | none   =>
      let n := ZDD.node v t e
      (n, {mgr with uniq := mgr.uniq.insert key n})

/--
  Computes the union (logical OR) of two ZDDs.

  The union operation represents the union of the families of sets:
  f ∪ g = {x | x ∈ f or x ∈ g}

  Implementation uses a recursive algorithm that handles:
  1. Terminal cases (⊥, ⊤)
  2. Variable ordering between nodes
  3. Recursive union on children with canonicalization via make_node

  Parameters:
  - mgr: The ZDD manager containing the unique table
  - f, g: The two ZDDs to union

  Returns:
  - A tuple of (resulting ZDD node, updated manager)
-/
partial def zdd_union (mgr : ZDDManager) (f g : ZDD) : ZDD × ZDDManager :=
  match f, g with
  | ZDD.terminal0, _ => (g, mgr)
  | _, ZDD.terminal0 => (f, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1  => (ZDD.terminal1, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zdd_union mgr t1 t2
      let (e, mgr) := zdd_union mgr e1 e2
      make_node mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zdd_union mgr t1 g
      let (e, mgr) := zdd_union mgr e1 g
      make_node mgr v1 t e
    else
      let (t, mgr) := zdd_union mgr f t2
      let (e, mgr) := zdd_union mgr f e2
      make_node mgr v2 t e

/--
  Computes the intersection (logical AND) of two ZDDs.

  The intersection operation represents the intersection of the families of sets:
  f ∩ g = {x | x ∈ f and x ∈ g}

  Implementation uses a recursive algorithm that handles:
  1. Terminal cases (⊥, ⊤)
  2. Variable ordering between nodes
  3. Recursive intersection on children with canonicalization via make_node

  Parameters:
  - mgr: The ZDD manager containing the unique table
  - f, g: The two ZDDs to intersect

  Returns:
  - A tuple of (resulting ZDD node, updated manager)
-/
partial def zdd_inter (mgr : ZDDManager) (f g : ZDD) : ZDD × ZDDManager :=
  match f, g with
  | ZDD.terminal0, _ | _, ZDD.terminal0  => (ZDD.terminal0, mgr)
  | ZDD.terminal1, ZDD.terminal1         => (ZDD.terminal1, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1  => (ZDD.terminal0, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zdd_inter mgr t1 t2
      let (e, mgr) := zdd_inter mgr e1 e2
      make_node mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zdd_inter mgr t1 g
      let (e, mgr) := zdd_inter mgr e1 g
      make_node mgr v1 t e
    else
      let (t, mgr) := zdd_inter mgr f t2
      let (e, mgr) := zdd_inter mgr f e2
      make_node mgr v2 t e

/--
  Computes the difference (f - g) of two ZDDs.

  The difference operation represents the set difference of the families of sets:
  f - g = {x | x ∈ f and x ∉ g}

  Implementation uses a recursive algorithm that handles:
  1. Terminal cases (⊥, ⊤)
  2. Variable ordering between nodes
  3. Recursive difference on children with canonicalization via make_node

  Parameters:
  - mgr: The ZDD manager containing the unique table
  - f, g: The two ZDDs for which to compute the difference

  Returns:
  - A tuple of (resulting ZDD node, updated manager)
-/
partial def zdd_diff (mgr : ZDDManager) (f g : ZDD) : ZDD × ZDDManager :=
  match f, g with
  | ZDD.terminal0, _ => (ZDD.terminal0, mgr)
  | _, ZDD.terminal0 => (f, mgr)
  | ZDD.terminal1, ZDD.terminal1 => (ZDD.terminal0, mgr)
  | ZDD.terminal1, _ => (ZDD.terminal1, mgr)
  | _, ZDD.terminal1 => (ZDD.terminal0, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zdd_diff mgr t1 t2
      let (e, mgr) := zdd_diff mgr e1 e2
      make_node mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zdd_diff mgr t1 g
      let (e, mgr) := zdd_diff mgr e1 g
      make_node mgr v1 t e
    else
      let (t, mgr) := zdd_diff mgr f t2
      let (e, mgr) := zdd_diff mgr f e2
      make_node mgr v2 t e

/--
  Counts the number of paths (satisfying assignments) in a ZDD.

  This function calculates the total number of sets represented by the ZDD by counting
  paths that lead to the terminal 1 node. Each path corresponds to a set in the
  family encoded by the ZDD.

  * For terminal 0 node: Returns 0 (represents empty family, no sets)
  * For terminal 1 node: Returns 1 (represents family with only the empty set)
  * For decision nodes: Returns sum of paths in both branches

  @param z The ZDD instance to analyze
  @return The number of distinct sets represented by the ZDD
-/
def countPaths' (z :ZDD) : Nat := match z with
  | ZDD.terminal0 => 0
  | ZDD.terminal1 => 1
  | ZDD.node _ t e => countPaths' t + countPaths' e

  -- Efficient countPaths with memoization
  partial def countPathsM (z : ZDD) (count : HashMap ZDD Nat := HashMap.emptyWithCapacity)  : Nat × HashMap ZDD Nat :=
    match count.get? z with
    | some n => (n, count)
    | none   =>
      let (n, count) :=
        match z with
        | ZDD.terminal0 => (0, count)
        | ZDD.terminal1 => (1, count)
        | ZDD.node _ t e =>
          let (nt, count) := countPathsM t count
          let (ne, count) := countPathsM e count
          (nt + ne, count)
      (n, count.insert z n)

def countPaths (z : ZDD) := countPathsM z |>.fst
