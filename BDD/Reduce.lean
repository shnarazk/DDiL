import Std.Data.HashMap
import Graph.Ref
import BDD.Basic

open Std

namespace BDD_reduce

abbrev RefMap := HashMap Ref Ref

variable (g : Graph)

/-- Trim nodes that have the same li and hi refs. -/
def trim (nodes : Array Node) (updatedRef : RefMap) (targets : Array Ref) : RefMap :=
  targets.foldl
    (fun updatedRef (ref: Ref) ↦
      let node := nodes[ref.link.get!]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi then updatedRef.insert ref li else updatedRef )
    updatedRef

/-- Merage nodes which have the same varId, li, hi -/
def merge (updatedRef : RefMap) (nodes : Array Node) (prev next : Ref)
    : RefMap × Array Node × Ref :=
  let prev := updatedRef.getD prev prev
  let next := updatedRef.getD next next
  let prevNode := nodes[prev.link.get!]!
  let nextNode := nodes[next.link.get!]!
  if prevNode == nextNode
    then (updatedRef.insert next prev, nodes, prev)
    else (updatedRef, nodes, next)

end BDD_reduce

/-- Rebuild the given `Graph g` as BDD. -/
def BDD.reduce (nv : Nat) (nodes : Array Node) (root : Ref) (var_nodes : HashMap Nat (Array Ref)) : BDD :=
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes, _) (_, refs) ↦
        let updatedRef := BDD_reduce.trim nodes updatedRef refs
        let nodes := refs.foldl
          (fun nodes ref ↦
            let n := nodes[ref.link.get!]!
            nodes.set!
              ref.link.get!
              {n with li := updatedRef.getD n.li n.li, hi := updatedRef.getD n.hi n.hi} )
          nodes
        let refs := refs.map (fun r ↦ updatedRef.getD r r)
          |>.insertionSort (fun r₁ r₂ ↦ if (nodes, r₁) < (nodes, r₂) then true else false)
        refs.foldl
          (fun (updatedRef, nodes, prev) next ↦ BDD_reduce.merge updatedRef nodes prev next)
          (updatedRef, nodes, Ref.to nodes.size) )
      (HashMap.empty, nodes, Ref.bool false)
    |> (fun (updatedRef, nodes, _) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes nv nodes
          -- let root := Ref.to g.nodes.size.pred
          {toGraph := g.compact (updatedRef.getD root root)}
        else
          default )

/-- Check the trivial cases. Otherwise pass to `reduce`. -/
def Graph.toBDD (g : Graph) : BDD :=
  -- build a mapping from `varId` to `List node`
  let nodes := g.nodes
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
    | _   , _    => BDD.reduce g.numVars nodes (Ref.last nodes) var_nodes
