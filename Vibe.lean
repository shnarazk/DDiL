import Std.Data.HashMap

open Std

inductive ZDD
| node : Nat → ZDD → ZDD → ZDD
| terminal0 : ZDD
| terminal1 : ZDD
deriving BEq, Hashable, Repr

def toStringZDD (z : ZDD) := match z with
    | ZDD.node v t e => s!"[ZDD: {v} {toStringZDD t} {toStringZDD e}]"
    | ZDD.terminal0 => "ZDD: 0"
    | ZDD.terminal1 => "ZDD: 1"

instance : ToString ZDD where
  toString := toStringZDD

structure ZDDManager where
  uniq : HashMap (Nat × ZDD × ZDD) ZDD
deriving Inhabited

def make_node (mgr : ZDDManager) (v : Nat) (t e : ZDD) : ZDD × ZDDManager :=
  if t == ZDD.terminal0 then
    (e, mgr)
  else if t == e then
    (t, mgr)
  else
    let key := (v, t, e)
    match mgr.uniq.get? key with
    | some n => (n, mgr)
    | none =>
      let n := ZDD.node v t e
      (n, { mgr with uniq := mgr.uniq.insert key n })

--
partial def zdd_union (mgr : ZDDManager) (f g : ZDD) : ZDD × ZDDManager :=
  match f, g with
  | ZDD.terminal0, _ => (g, mgr)
  | _, ZDD.terminal0 => (f, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1 => (ZDD.terminal1, mgr)
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
--
partial def zdd_inter (mgr : ZDDManager) (f g : ZDD) : ZDD × ZDDManager :=
  match f, g with
  | ZDD.terminal0, _ | _, ZDD.terminal0 => (ZDD.terminal0, mgr)
  | ZDD.terminal1, ZDD.terminal1 => (ZDD.terminal1, mgr)
  | ZDD.terminal1, _ | _, ZDD.terminal1 => (ZDD.terminal0, mgr)
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

--
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

--
def main : IO Unit :=
  let mgr := { uniq := HashMap.emptyWithCapacity }
  let (a, mgr) := make_node mgr 0 ZDD.terminal1 ZDD.terminal0
  let (b, mgr) := make_node mgr 1 ZDD.terminal1 ZDD.terminal0
  let (u, _mg) := zdd_union mgr a b
  IO.println s!"Union: {u}"
