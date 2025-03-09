import Common.Graph
import BDD.Basic

namespace Test_BDD
def independent_bdd : BDD :=
  TreeNode.fromString
      "{  { { {{{T T} {T F}} {{T T} {F F}}}
              {{{T T} {T F}} {{F F} {F F}}} }
            { {{{T T} {T F}} {{T T} {F F}}}
              {{{F F} {F F}} {{F F} {F F}}} } }
          { { {{{T F} {T F}} {{T F} {F F}}}
              {{{T F} {T F}} {{F F} {F F}}} }
            { {{{F F} {F F}} {{F F} {F F}}}
              {{{F F} {F F}} {{F F} {F F}}} } } }"
    |> Graph.fromTreeNode
    |>.toBDD

/- def g1 : Graph := {
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

def g_independent : Graph := ↑(TreeNode.ofString
  "{ 1
    { 2
      { 3
        {4 {5 {6 T T} {6 T F}} {5 {6 T T} {6 F F}}}
        {4 {5 {6 T T} {6 T F}} {5 {6 F F} {6 F F}}} }
      { 3
        {4 {5 {6 T T} {6 T F}} {5 {6 T T} {6 F F}}}
        {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}} } }
    { 2
      { 3
        {4 {5 {6 T F} {6 T F}} {5 {6 T F} {6 F F}}}
        {4 {5 {6 T F} {6 T F}} {5 {6 F F} {6 F F}}} }
      { 3
        {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}}
        {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}} } } }")

def bdd1 : BDD := ↑g1
def bdd2 : BDD := ↑g2
def independent : BDD := ↑g_independent
-/
def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println beg
  IO.println s!"BDD.independent.shape: {GraphShape.shapeOf independent_bdd}"
  -- IO.println s!"BDD: {(↑g1 : BDD)}"
  -- IO.println s!"bdd1.reduce: {bdd1.reduce.toHashMap.toList}"
  -- IO.println s!"bdd2: {bdd2.toHashMap.toList}"
  -- IO.println s!"bdd2.reduce: {bdd2.reduce.toHashMap.toList}"
  -- IO.println s!"BDD.congruent g1 ≃ g1: {Graph.is_congruent g1 g1}"
  -- IO.println s!"BDD.congruent g1 ≃ g2: {Graph.is_congruent g1 g2}"
  -- if let some message ← independent.reduce.toGraph.dumpAsPng "lake-test_independent-bdd.png"
  --   then IO.println message
  try
    let file ← independent_bdd.dumpAsPng "lake-test_bdd1.png"
    IO.println s!"Graph g₂ dumped as: {file}"
  catch e => IO.println s!"Error: {e}"
  IO.println fin
  return ()

end Test_BDD
