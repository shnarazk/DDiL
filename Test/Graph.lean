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

def run : IO Unit := do
  IO.println s!"Graph: {(g1, 2)}"
  IO.println s!"Graph: {(g1, 3)}"
  IO.println s!"Graph.toHashMap: {g1.toHashMap.toList}"
  IO.println s!"Graph.toHashSet: {g1.toHashSet.toList}"

end Test_Graph
