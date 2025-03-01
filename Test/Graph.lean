import Common.Graph
import Common.Node

namespace Test_Graph

def g1 : Graph := {
  nodes := #[
     .isFalse,
     .isTrue,
     .node 1 0 3,
     .node 2 1 0],
  root := Fin.ofNat' 4 2,
  filled := by exact Nat.instNeZeroSucc
}

def g2 : Graph := {
  nodes := #[
     .isFalse,
     .isTrue,
     .node 1 3 4,
     .node 2 0 0,
     .node 2 1 0],
  root := Fin.ofNat' 5 2,
  filled := by exact Nat.instNeZeroSucc
}

def run : IO Unit := do
  IO.println s!"Graph: {(g1, 2)}"
  IO.println s!"Graph: {(g1, 3)}"
  IO.println s!"Graph.toHashMap: {g1.toHashMap.toList}"
  IO.println s!"Graph.toHashSet: {g1.toHashSet.toList}"
  IO.println s!"g1 ≃ g1: {Graph.is_congruent g1 g1}"
  IO.println s!"g1 ≃ g2: {Graph.is_congruent g1 g2}"

end Test_Graph
