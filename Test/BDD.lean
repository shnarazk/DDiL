import Common.Graph
import Common.Node
import BDD.Basic

namespace Test_BDD

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

def bdd1 : BDD := ↑g1
def bdd2 : BDD := ↑g2

def run : IO Unit := do
  IO.println s!"BDD: {(↑g1 : BDD)}"
  IO.println s!"bdd1.reduce: {bdd1.reduce.toHashMap.toList}"
  IO.println s!"bdd2: {bdd2.toHashMap.toList}"
  IO.println s!"bdd2.reduce: {bdd2.reduce.toHashMap.toList}"
  IO.println s!"BDD.congruent g1 ≃ g1: {Graph.is_congruent g1 g1}"
  IO.println s!"BDD.congruent g1 ≃ g2: {Graph.is_congruent g1 g2}"
  bdd2.reduce.toGraph.dumpAsDot "lake-test_bdd2-reduced.gv"
  try
    IO.println =<< IO.Process.run {
      cmd := "dot",
      args := #["-T", "png", "-o", "lake-test_bdd2-reduced.gv"]}
  catch
    | e => IO.println s!"Failed to make a png: {e}"

end Test_BDD
