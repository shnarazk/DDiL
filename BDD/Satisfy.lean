import Graph.Ref
import Graph.Base
import BDD.Base

namespace BDD_satisfy_private

partial def satisfy_graph (g : Graph) (root : Ref) (exp : List Int) : Bool := match root, exp with
  | {grounded := b, link := none},    _ => b
  | {grounded := _, link := some l}, [] =>
    let node := g.nodes[l]!
    satisfy_graph g node.li [] || satisfy_graph g node.hi []
  | {grounded := _, link := some l}, (x :: xs) =>
    let node := g.nodes[l]!
    match compare node.varId x.natAbs with
      | Ordering.lt => satisfy_graph g node.li exp || satisfy_graph g node.hi exp
      | Ordering.eq => satisfy_graph g (if x < 0 then node.li else node.hi) xs
      | Ordering.gt => (x < 0) && satisfy_graph g root xs

end BDD_satisfy_private

def BDD.isSatisfiedBy (bdd : BDD) (exp : List Int) : Bool :=
  if let some b := bdd.asBool
  then b
  else BDD_satisfy_private.satisfy_graph ↑bdd (Ref.last bdd.nodes) exp
