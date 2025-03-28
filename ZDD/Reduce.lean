import Std.Data.HashMap
import Graph.Basic
import Graph.Ref
import BDD.Basic
import ZDD.Basic

open Std

namespace ZDD_reduce

abbrev RefMap := HashMap Ref Ref

variable (g : Graph)

/-- insert intermediate nodes -/
def insert (g : Graph) : Array Node :=
  let nodes := (dbg? "ZDD.Reduce.insert src" g.nodes).zipIdx.foldl
    (fun nodes (node, ix) ↦
      let nodes := match node.li.link with
        | none => nodes
        | some next =>
          let seq := List.range' node.varId.succ (nodes[next]!.varId - node.varId.succ)
          if seq.isEmpty
            then nodes
            else
              let nodes := seq.foldl
                (fun nodes i => nodes.push {varId := i, li := Ref.to nodes.size.succ, hi := Ref.to nodes.size.succ})
                (nodes.set! ix {node with li := Ref.to nodes.size})
              nodes.modify nodes.size.pred (fun n ↦ {n with li := Ref.to next, hi := Ref.to next})
      let nodes := match node.hi.link with
        | none => nodes
        | some next =>
          let seq := List.range' node.varId.succ (nodes[next]!.varId - node.varId.succ)
          if seq.isEmpty
            then nodes
            else
              let node := nodes[ix]!
              let nodes := seq.foldl
                (fun nodes i => nodes.push {varId := i, li := Ref.to nodes.size.succ, hi := Ref.to nodes.size.succ})
                (nodes.set! ix {node with hi := Ref.to nodes.size})
              nodes.modify nodes.size.pred (fun n ↦ {n with li := Ref.to next, hi := Ref.to next})
      nodes )
    g.nodes
  dbg? "ZDD.Reduce.insert returns" nodes

private partial def goDown (nodes : Array Node) (root : Ref) : Ref := match root with
  | {grounded := _, link := none} => root
  | {grounded := _, link := some i} => match nodes[i]! with
    | {varId := _, li := li, hi := {grounded := false, link := none}} => goDown nodes li
    | _ => root

partial def trim (nodes : Array Node) (root : Ref := Ref.last nodes) : Array Node :=
  match root.link with
  | none   => nodes
  | some i =>
    let node := nodes[i]!
    let ref := goDown nodes node.hi
    let nodes := nodes.set! i {nodes[i]! with hi := ref}
    trim (trim nodes node.li) ref

/-- FIXME: TRIM nodes which hi points to `false` AND REFERED BY UPSTREAM.hi.
Probably top-down transforming is the best. -/
def trim_old (updatedRef : RefMap) (targets : Array Ref) : RefMap × Array Ref :=
  targets.foldl
    (fun (updatedRef, acc) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if hi == Ref.bool false
      then dbg! s!"trim {ref} to {node.li}/{li}" (updatedRef.insert ref li, acc)
      else (updatedRef, acc.push ref) )
    (updatedRef, #[])

/-- Merage nodes which have the same varId, li, hi -/
def merge (updatedRef : RefMap) (nodes : Array Node) (prev next : Ref) : RefMap × Array Node × Ref :=
  let prev := updatedRef.getD prev prev
  let next := updatedRef.getD next next
  let prevNode := nodes[prev.link.get!]!
  let nextNode := nodes[next.link.get!]!
  if prevNode == nextNode
  then dbg! s!"merge {next} to {prev}" (updatedRef.insert next prev, nodes, prev)
  else (updatedRef, nodes, next)

end ZDD_reduce

/-- Rebuild the given non-normalized `Graph g` as ZDD. -/
def ZDD.reduce (nv : Nat) (nodes : Array Node) (root : Ref) (var_nodes : HashMap Nat (Array Ref)) : ZDD :=
  (dbg? "var_nodes" var_nodes).toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes, _) (_, refs) ↦
        /- reorder refs -/
        -- let (updatedRef, targets) := ZDD_reduce.trim g updatedRef refs
        let nodes := refs.foldl
          (fun nodes ref ↦
            let n := nodes[ref.link.get!]!
            nodes.set!
              ref.link.get!
              {n with li := updatedRef.getD n.li n.li, hi := updatedRef.getD n.hi n.hi} )
          nodes
        let refs := refs.map (fun r ↦ updatedRef.getD r r)
          |>.insertionSort (fun r₁ r₂ ↦ nodes[r₁.link.get!]! < nodes[r₂.link.get!]!)
        (dbg? s!"refs: {refs.map (nodes[·.link.get!]!)}" refs).foldl
          (fun (updatedRef, nodes, prev) next ↦ ZDD_reduce.merge updatedRef nodes prev next)
          (updatedRef, nodes, Ref.to nodes.size) )
      (HashMap.empty, nodes, Ref.bool false)
    |> (fun (updatedRef, nodes, _) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes nv nodes
          {toGraph := g.compact (updatedRef.getD root root)}
        else
          default )

/-- Convert a Graph to ZDD.
Presume: no holes between lined var pairs. This condition holds by invoking `toBDD`.
-/
def Graph.toZDD₂ (g : Graph) : ZDD :=
  -- build a mapping from `varId` to `List node`
  let nodes := ZDD_reduce.trim g.nodes
    |> dbg? "trimmed"
    |> Graph_compact.compact
    |> dbg? "compacted"
  let (all_false, all_true, var_nodes) := nodes.zipIdx.foldl
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
    | _   , _    => ZDD.reduce g.numVars nodes (Ref.last nodes) var_nodes |> dbg? "ZDD.Reduce.Graph.toZDD₂ returns"
