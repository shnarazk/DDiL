import Std.Data.HashMap
import Graph.Basic
import Graph.Ref
import BDD.Basic
import ZDD.Basic

open Std

namespace ZDD_reduce

abbrev RefMap := HashMap Ref Ref

variable (g : Graph)

/-- instert intermediate nodes -/
private def insert (updatedRef : RefMap) (targets : Array Ref) : RefMap × Array Ref :=
  -- FIXME: do it
  (updatedRef, targets)

/-- TRIM nodes which hi points to `false` -/
private def transform (updatedRef: RefMap) (targets: Array Ref) : Array Ref × RefMap :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if hi == Ref.bool false
      then
        (acc, updatedRef.insert ref li)
      else
        let seq := match li.link with
          | none   => List.range' node.varId.succ (g.numVars - node.varId)
          | some k => List.range' node.varId.succ (g.nodes[k]!.varId - node.varId)
        seq.foldl -- insert intermediate nodes.
          (fun acc _ ↦ acc)
          (acc, updatedRef) )
    (#[], updatedRef)

/-- Merage nodes which have the same varId, li, hi -/
private def merge (updatedRef: RefMap) (nodes: Array Node) (prev next : Ref) : RefMap × Array Node × Ref :=
  let prevNode := nodes.getD (prev.link.getD 0) default
  let nextNode : Node := nodes[next.link.getD 0]!
  let node' : Node := { nextNode with
    li := updatedRef.getD nextNode.li nextNode.li
    hi := updatedRef.getD nextNode.hi nextNode.hi }
  if prevNode == node'
    then (updatedRef.insert next prev, nodes, prev)
    else (updatedRef, nodes.set! (next.link.getD 0) node', next)

end ZDD_reduce

/-- Rebuild the given non-normalized `Graph g` as ZDD. -/
def ZDD.reduce (g : Graph) (var_nodes: HashMap Nat (Array Ref)) : ZDD :=
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes, _) (_, refs) ↦
        let (targets, updatedRef) := ZDD_reduce.transform g updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prev) next ↦ ZDD_reduce.merge updatedRef nodes prev next)
            (updatedRef, nodes, Ref.to nodes.size) )
      (HashMap.empty, g.nodes, Ref.bool false)
    |> (fun (updatedRef, nodes, _) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes g.numVars nodes
          let root := Ref.last g.nodes
          {toGraph := g.compact (updatedRef.getD root root)}
        else
          default )

/-- Check the trivial cases. Otherwise pass to `reduce`. -/
def Graph.toZDD (g : Graph) : ZDD :=
  -- build a mapping from `varId` to `List node`
  let (all_false, all_true, var_nodes) := g.nodes.zipIdx.foldl
    (fun (falses, trues, mapping) (node, i) =>
     ( falses && (node.asBool == some false),
       trues && (node.asBool == some true),
       mapping.alter
         node.varId
         (fun list => match list with
           | none => some #[Ref.to i]
           | some l => some (l.push (Ref.to i)) )))
    (true, true, (HashMap.empty : HashMap Nat (Array Ref)))
  match all_false, all_true with
    | true, _    => ↑{(default : Graph) with constant := false}
    | _   , true => ↑{(default : Graph) with constant := true}
    | _   , _    => ZDD.reduce g var_nodes

/-- Rebuild the given bdd-encoded `Graph g` as ZDD. -/
def ZDD.convert (bdd : BDD) (var_nodes: HashMap Nat (Array Ref)) : ZDD :=
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes, _) (_, refs) ↦
        let (targets, updatedRef) := ZDD_reduce.transform bdd updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prev) next ↦ ZDD_reduce.merge updatedRef nodes prev next)
            (updatedRef, nodes, Ref.to nodes.size) )
      (HashMap.empty, bdd.nodes, Ref.bool false)
    |> (fun (updatedRef, nodes, _) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes bdd.numVars nodes
          let root := Ref.last g.nodes
          {toGraph := g.compact (updatedRef.getD root root)}
        else
          default )

/-- Check the trivial cases. Otherwise pass to `reduce`. -/
def BDD.toZDD (bdd : BDD) : ZDD :=
  -- build a mapping from `varId` to `List node`
  let (all_false, all_true, var_nodes) := bdd.nodes.zipIdx.foldl
    (fun (falses, trues, mapping) (node, i) =>
     ( falses && (node.asBool == some false),
       trues && (node.asBool == some true),
       mapping.alter
         node.varId
         (fun list => match list with
           | none => some #[Ref.to i]
           | some l => some (l.push (Ref.to i)) )))
    (true, true, (HashMap.empty : HashMap Nat (Array Ref)))
  match all_false, all_true with
    | true, _    => ↑{(default : Graph) with constant := false}
    | _   , true => ↑{(default : Graph) with constant := true}
    | _   , _    => ZDD.convert bdd var_nodes
