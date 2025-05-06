import Std.Data.HashMap
import ZDD.Basic

open Std

/--
Creates a new ZDD node with zero-suppression rules applied.
1. If then-child is `terminal0`, return else-child.
2. If then-child equals else-child, return either.
3. Otherwise, create or reuse a unique node via the manager.
-/
def makeNode (mgr : ZDD.manager) (v : VarIndex) (t e : ZDD) : ZDD × ZDD.manager :=
  if t == ZDD.terminal0 then
    (e, mgr)
  else
    let key := (v, t, e)
    match mgr.get? key with
    | some n => (n, mgr)
    | none   =>
      let n := ZDD.node v t e
      (n, mgr.insert key n)

/--
Computes the union (logical OR) of two ZDDs.
f ∪ g = {x | x ∈ f or x ∈ g}
-/
partial def zddUnion (mgr : ZDD.manager) (f g : ZDD) : ZDD × ZDD.manager :=
  match f, g with
  | ZDD.terminal0, _ => (g, mgr)
  | _, ZDD.terminal0 => (f, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1 => (ZDD.terminal1, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zddUnion mgr t1 t2
      let (e, mgr) := zddUnion mgr e1 e2
      makeNode mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zddUnion mgr t1 g
      let (e, mgr) := zddUnion mgr e1 g
      makeNode mgr v1 t e
    else
      let (t, mgr) := zddUnion mgr f t2
      let (e, mgr) := zddUnion mgr f e2
      makeNode mgr v2 t e

/--
Computes the intersection (logical AND) of two ZDDs.
f ∩ g = {x | x ∈ f and x ∈ g}
-/
partial def zddInter (mgr : ZDD.manager) (f g : ZDD) : ZDD × ZDD.manager :=
  match f, g with
  | ZDD.terminal0, _ | _, ZDD.terminal0 => (ZDD.terminal0, mgr)
  | ZDD.terminal1, ZDD.terminal1        => (ZDD.terminal1, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1 => (ZDD.terminal0, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zddInter mgr t1 t2
      let (e, mgr) := zddInter mgr e1 e2
      makeNode mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zddInter mgr t1 g
      let (e, mgr) := zddInter mgr e1 g
      makeNode mgr v1 t e
    else
      let (t, mgr) := zddInter mgr f t2
      let (e, mgr) := zddInter mgr f e2
      makeNode mgr v2 t e

/--
Computes the difference (f - g) of two ZDDs.
f - g = {x | x ∈ f and x ∉ g}
-/
partial def zddDiff (mgr : ZDD.manager) (f g : ZDD) : ZDD × ZDD.manager :=
  match f, g with
  | ZDD.terminal0, _                 => (ZDD.terminal0, mgr)
  | _, ZDD.terminal0                 => (f, mgr)
  | ZDD.terminal1, ZDD.terminal1     => (ZDD.terminal0, mgr)
  | ZDD.terminal1, _                 => (ZDD.terminal1, mgr)
  | _, ZDD.terminal1                 => (ZDD.terminal0, mgr)
  | ZDD.node v1 t1 e1, ZDD.node v2 t2 e2 =>
    if v1 == v2 then
      let (t, mgr) := zddDiff mgr t1 t2
      let (e, mgr) := zddDiff mgr e1 e2
      makeNode mgr v1 t e
    else if v1 < v2 then
      let (t, mgr) := zddDiff mgr t1 g
      let (e, mgr) := zddDiff mgr e1 g
      makeNode mgr v1 t e
    else
      let (t, mgr) := zddDiff mgr f t2
      let (e, mgr) := zddDiff mgr f e2
      makeNode mgr v2 t e

/--
Counts the number of paths (satisfying assignments) in a ZDD.
-/
def countPaths' (z : ZDD) : Nat :=
  match z with
  | ZDD.terminal0 => 0
  | ZDD.terminal1 => 1
  | ZDD.node _ t e => countPaths' t + countPaths' e

/--
Efficient path counting with memoization.
-/
partial def countPathsM (z : ZDD) (count : HashMap ZDD Nat := HashMap.emptyWithCapacity) : Nat × HashMap ZDD Nat :=
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

/--
Returns the total number of paths in the ZDD.
-/
def countPaths (z : ZDD) : Nat :=
  (countPathsM z).fst

/--
Adds a new node to the ZDD and unions it with the existing diagram.
-/
def addNode (z : ZDD) (vi : VarIndex) (f t : ZDD) : ZDD :=
  let mgr := (↑z : ZDDManager)
  let (newZ, mgr') := makeNode mgr vi f t
  (zddUnion mgr' z newZ).fst
