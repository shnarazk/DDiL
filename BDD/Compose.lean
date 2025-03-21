import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Graph.Basic
import BDD.Reduce

open Std

namespace BDD_compose

abbrev Nodes := Array Node
abbrev Key := HashMap (Ref × Ref × Ref) Ref
abbrev Evaluation := HashMap Ref Bool

variable (g : Graph)

def or  := MergeFunction.of (· || ·) (some (true, true))
def and := MergeFunction.of (· && ·) (some (false, false))
def not : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

def varId (nodes : Array Node) (ref : Ref) : Option Nat :=
  match ref.link with
    | none => none
    | some i => some nodes[i]!.varId

def goDown (nodes : Array Node) (ref : Ref) : Ref × Ref :=
  match ref.link with
    | none => (ref, ref)
    | some i => (nodes[i]!.li, nodes[i]!.hi)

partial def step (v1l v1h v2 : Ref) (vi : Nat) (nodes : Nodes) (key : Key) (evaluation : Evaluation)
    : Ref × Nodes × Key × Evaluation :=

  -- Perform restrictions
  let v1l := if let some i := v1l.link then
      let node := nodes[i]!
      if node.varId == vi then node.li else v1l
    else v1l
  let v1h := if let some i := v1h.link then
      let node := nodes[i]!
      if node.varId == vi then node.hi else v1h
    else v1h

  -- Apply operation ITE
  if let some u := key[(v1l, v1h, v2)]? then
    (u, nodes, key, evaluation) -- have already evaluated
  else if let some value := or.apply
      (and.apply (not v2.asBool) v1l.asBool)
      (and.apply v2.asBool v1h.asBool)
  then
    let r := Ref.bool value
    (r, nodes, key.insert (v1l, v1h, v2) r, evaluation.insert r value)
  else if let some vi := [v1l, v1h, v2].map (varId nodes ·) |>.filterMap id |>.min? then
    -- create nonterminal and evalate further down
    let (v1ll, v1lh) := if vi == varId nodes v1l then goDown nodes v1l else (v1l, v1l)
    let (v1hl, v1hh) := if vi == varId nodes v1h then goDown nodes v1h else (v1h, v1h)
    let (v2l, v2h)   := if vi == varId nodes v2  then goDown nodes v2  else (v2, v2)
    let (l, nodes, key, evaluation) := step v1ll v1hl v2l vi nodes key evaluation
    let (h, nodes, key, evaluation) := step v1lh v1hh v2h vi nodes key evaluation
    let r := Ref.to nodes.size
    (r, nodes.push {varId := vi, li := l, hi := h}, key.insert (v1l, v1h, v2) r, evaluation)
  else
    dbg "error" (v2, nodes, key, evaluation)

end BDD_compose

def BDD.compose (self other : BDD) (varIndex : Nat) : BDD :=
  let r1 := Ref.to self.toGraph.nodes.size.pred
  let all_nodes : Array Node := Node.append_nodes ↑self ↑other
  let r2 := Ref.to all_nodes.size.pred
  BDD_compose.step r1 r1 r2 varIndex all_nodes HashMap.empty HashMap.empty
    |> (fun (_root, (nodes : Array Node), _, _) ↦ if nodes.isEmpty
        then default
        else Graph.fromNodes (Nat.max self.numVars other.numVars) nodes )
    |> (·.compact.toBDD)
