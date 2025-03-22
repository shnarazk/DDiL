import Std.Data.HashMap
import Graph.Basic
import Graph.Ref
import ZDD.Basic

open Std

namespace ZDD_reduce

abbrev RefMap := HashMap Ref Ref

variable (g : Graph)

/-- Trim nodes which hi points to `false`. -/
def trim (updatedRef: RefMap) (targets: Array Ref) : Array Ref × RefMap :=
  targets.foldl
    (fun (acc, updatedRef) (ref: Ref) ↦
      let node := g.nodes[ref.link.getD 0]!
      let li := updatedRef.getD node.li node.li
      let hi := updatedRef.getD node.hi node.hi
      if hi == Ref.bool false then (acc, updatedRef.insert ref li) else (acc.push ref, updatedRef) )
    (#[], updatedRef)

/-- Merago nodes which have the same varId, li, hi -/
def merge (updatedRef: RefMap) (nodes: Array Node) (prev next : Ref) : RefMap × Array Node × Ref :=
  let prevNode := nodes.getD (prev.link.getD 0) default
  let nextNode : Node := nodes[next.link.getD 0]!
  let node' : Node := { nextNode with
    li := updatedRef.getD nextNode.li nextNode.li
    hi := updatedRef.getD nextNode.hi nextNode.hi }
  if prevNode == node'
    then (updatedRef.insert next prev, nodes, prev)
    else (updatedRef, nodes.set! (next.link.getD 0) node', next)

end ZDD_reduce

/-
fn reduce(&mut self) {
    let root = &self.graph;
    let (mut index, mut node) = Node::build_indexer(&[root.clone()]);
    let mut vlist: HashMap<usize, Vec<&Node>> = HashMap::new();
    // put each vertex u on list vlist[u.var_index]
    for n in root.all_nodes().iter().cloned() {
        vlist.entry(n.unified_key()).or_default().push(n);
    }
    let mut next_id: usize = 2;
    for vi in vlist.keys().sorted().rev() {
        let mut q: Vec<((usize, usize), &Node)> = Vec::new();
        for node in vlist[vi].iter().cloned() {
            match **node {
                Vertex::Bool(_) => (),
                Vertex::Var {
                    ref low, ref high, ..
                } => {
                    if index[high] == 0 {
                        // redundant vertex
                        index.insert(node.clone(), index[low]);
                    } else {
                        q.push(((index[low], index[high]), node));
                    }
                }
            }
        }
        q.sort_unstable_by_key(|(k, _)| *k);
        let mut old_key: (usize, usize) = (usize::MAX, usize::MAX);
        for (key, n) in q.iter().cloned() {
            if key == old_key {
                index.insert(n.clone(), next_id);
            } else {
                next_id += 1;
                match **n {
                    Vertex::Bool(_) => {
                        index.insert(n.clone(), next_id);
                        node.insert(next_id, n.clone());
                    }
                    Vertex::Var {
                        var_index,
                        ref low,
                        ref high,
                    } => {
                        let nn = Node::new_var(
                            var_index,
                            node[&index[low]].clone(),
                            node[&index[high]].clone(),
                        );
                        index.insert(n.clone(), next_id);
                        index.insert(nn.clone(), next_id);
                        node.insert(next_id, nn);
                    }
                }
                old_key = key;
            }
        }
    }
    // pick up a tree from the hash-table
    self.graph = node[&next_id].clone();
}
-/
/-- Called from `reduce`. Rebuild and merge mergeable nodes. -/
def ZDD.reduce (g : Graph) (var_nodes: HashMap Nat (Array Ref)) : ZDD :=
  -- let root := Ref.last g.nodes
  var_nodes.toList.mergeSort (fun a b ↦ a.fst > b.fst) -- from bottom var to top var
    |>.foldl
      (fun (updatedRef, nodes) (_, refs) ↦
        let (targets, updatedRef) := ZDD_reduce.trim g updatedRef refs
        targets.foldl
            (fun (updatedRef, nodes, prev) next ↦ ZDD_reduce.merge updatedRef nodes prev next)
            (updatedRef, nodes, Ref.to nodes.size)
          |> (fun (updateRef, nodes, _) ↦ (updateRef, nodes)) )
      (HashMap.empty, g.nodes)
    |> (fun (updatedRef, nodes) ↦ if 0 < nodes.size then
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
