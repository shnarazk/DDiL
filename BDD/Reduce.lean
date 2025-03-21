import Std.Data.HashMap
import Graph.Ref
import BDD.Basic

open Std

namespace BDD_reduce

abbrev RefMap := HashMap Ref Ref

variable (g : Graph)

/-- Trim nodes that have the same li and hi refs. -/
def trim (updatedRef: RefMap) (targets: Array Ref) : Array Ref × RefMap :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if li == hi then (acc, updatedRef.insert ref li) else (acc.push ref, updatedRef) )
    (#[], updatedRef)

def merge (updatedRef: RefMap) (nodes: Array Node) (prev next : Ref) : RefMap × Array Node × Ref :=
  let prevNode := nodes.getD (prev.link.getD 0) default
  let nextNode : Node := nodes[next.link.getD 0]!
  let node' : Node := { nextNode with
    li := updatedRef.getD nextNode.li nextNode.li
    hi := updatedRef.getD nextNode.hi nextNode.hi }
  if prevNode == node'
    then (updatedRef.insert next prev, nodes, prev)
    else (updatedRef, nodes.set! (next.link.getD 0) node', next)

end BDD_reduce

/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def BDD.reduce (g : Graph) (var_nodes: HashMap Nat (Array Ref)) : BDD :=
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes) (_, refs) ↦
        let (targets, updatedRef) := BDD_reduce.trim g updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prev) next ↦ BDD_reduce.merge updatedRef nodes prev next)
            (updatedRef, nodes, Ref.to nodes.size)
          |> (fun (updateRef, nodes, _) ↦ (updateRef, nodes)) )
      (HashMap.empty, g.nodes)
    |> (fun (updatedRef, nodes) ↦ if 0 < nodes.size then
          let g := Graph.fromNodes g.numVars nodes
          let root := Ref.to g.nodes.size.pred
          {toGraph := g.compact (updatedRef.getD root root)}
            -- |> dbg s!"BDD.reduce {root}({rn}) => {updatedRef[root]?}"
        else
          default )

/-- Check the trivial cases. Otherwise pass to `reduce`. -/
def Graph.toBDD (g : Graph) : BDD :=
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
    | _   , _    => BDD.reduce g var_nodes
