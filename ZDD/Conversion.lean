import Std.Data.HashMap
import Graph.Basic
import Graph.Ref
import BDD.Basic
import ZDD.Basic
import ZDD.Reduce
import Graph.Reorder

open Std

namespace ZDD_conversion

def startFromOne (nodes : Array Node) (root : Ref := Ref.last nodes) : Option Node :=
  match root.link with
  | none => none
  | some i =>
    if nodes[i]!.varId == 1
    then none
    else some {varId := 1, li := root, hi := root}

/-- insert intermediate nodes -/
def insert (g : Graph) : Array Node :=
  let nodes := (dbg? "ZDD.Reduce.insert src" g.nodes).zipIdx.foldl
    (fun nodes (node, ix) ↦
      let seq := List.range' node.varId.succ (if let some next := node.li.link then nodes[next]!.varId - node.varId.succ else g.numVars - node.varId)
      let nodes := if seq.isEmpty then
          nodes
        else
          seq.foldl
              (fun nodes i ↦ nodes.push {varId := i, li := Ref.to nodes.size.succ, hi := Ref.to nodes.size.succ})
              (nodes.modify ix (fun n ↦ {n with li := Ref.to nodes.size}))
            |> (fun nodes ↦ nodes.modify nodes.size.pred (fun n ↦ {n with li := node.li, hi := node.li}))
      let seq := List.range' node.varId.succ (if let some next := node.hi.link then nodes[next]!.varId - node.varId.succ else g.numVars - node.varId)
      let nodes := if seq.isEmpty then
          nodes
        else
          seq.foldl
              (fun nodes i ↦ nodes.push {varId := i, li := Ref.to nodes.size.succ, hi := Ref.to nodes.size.succ})
              (nodes.modify ix (fun n ↦ {n with hi := Ref.to nodes.size}))
            |> (fun nodes ↦ nodes.modify nodes.size.pred (fun n ↦ {n with li := node.hi, hi := node.hi}))
      nodes )
    g.nodes
  dbg? "ZDD.Reduce.insert returns" nodes

/-- Rebuild the given bdd-encoded `Graph g` as ZDD. -/
def convert (bdd : BDD) (var_nodes: HashMap Nat (Array Ref)) : ZDD :=
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes, _) (_, refs) ↦
        -- let (updatedRef, targets) := ZDD_reduce.trim bdd updatedRef refs
        refs.foldl
          (fun (updatedRef, nodes, prev) next ↦ ZDD_reduce.merge updatedRef nodes prev next)
          (updatedRef, nodes, Ref.to nodes.size) )
      (HashMap.empty, bdd.nodes, Ref.bool false)
    |> (fun (updatedRef, nodes, _) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes bdd.numVars nodes
          let root := Ref.last g.nodes
          {toGraph := g.compact (updatedRef.getD root root)}
        else
          default )

end ZDD_conversion

def BDD.startFromOne (bdd : BDD) : BDD :=
  if let some n := ZDD_conversion.startFromOne bdd.toGraph.nodes
  then bdd.addNode n |>.fst
  else bdd

-- /-- Check the trivial cases. Otherwise pass to `reduce`. -/
-- def Graph.toZDD (g : Graph) : Graph :=
--   -- build a mapping from `varId` to `List node`
--   let bdd := ZDD_fromBDD.startFromOne g
--   let (all_false, all_true, var_nodes) := bdd.toGraph.nodes.zipIdx.foldl
--     (fun (falses, trues, mapping) (node, i) =>
--      ( falses && (node.asBool == some false),
--        trues && (node.asBool == some true),
--        mapping.alter
--          node.varId
--          (fun list => match list with
--            | none => some #[Ref.to i]
--            | some l => some (l.push (Ref.to i)) )))
--     (true, true, (HashMap.empty : HashMap Nat (Array Ref)))
--   match all_false, all_true with
--     | true, _    => ↑{(default : Graph) with constant := false}
--     | _   , true => ↑{(default : Graph) with constant := true}
--     | _   , _    => ZDD_fromBDD.convert bdd var_nodes

-- /-- Check the trivial cases. Otherwise pass to `reduce`. -/
-- def BDD.toZDD' (bdd : BDD) : ZDD :=
--   -- build a mapping from `varId` to `List node`
--   let bdd := bdd.startFromOne
--   let (all_false, all_true, var_nodes) := bdd.toGraph.nodes.zipIdx.foldl
--     (fun (falses, trues, mapping) (node, i) =>
--      ( falses && (node.asBool == some false),
--        trues && (node.asBool == some true),
--        mapping.alter
--          node.varId
--          (fun list => match list with
--            | none => some #[Ref.to i]
--            | some l => some (l.push (Ref.to i)) )))
--     (true, true, (HashMap.empty : HashMap Nat (Array Ref)))
--   match all_false, all_true with
--     | true, _    => ↑{(default : Graph) with constant := false}
--     | _   , true => ↑{(default : Graph) with constant := true}
--     | _   , _    => ZDD_conversion.convert bdd var_nodes

    def BDD.toZDD (bdd : BDD) : ZDD :=
      let bdd := dbg! "start from one" <| bdd.startFromOne
      let nodes := dbg! "insert intermediate nodes" <| ZDD_conversion.insert bdd.toGraph
      let g := Graph.reorderNodes bdd.numVars nodes (Ref.last bdd.toGraph.nodes)
      g.toZDD₂
