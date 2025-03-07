import Common.Debug
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

def g3 : Graph := {
  nodes := #[
     .isFalse,
     .isTrue,
     .node 1 3 4,
     .node 2 0 0,
     .node 2 1 0,
     .node 2 0 0,
     .node 2 1 1],
  root := Fin.ofNat' 7 2,
  filled := by exact Nat.instNeZeroSucc
}

def independent : Graph := ↑(TreeNode.ofString
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

def run : IO Unit := do
  let (start, done) := LogKind.warn.color
  IO.println start
  IO.println s!"Graph: {(g1, 2)}"
  IO.println s!"Graph: {(g1, 3)}"
  IO.println s!"Graph.toHashMap: {g1.toHashMap.toList}"
  IO.println s!"Graph.toHashSet: {g1.toHashSet.toList}"
  IO.println s!"g1 ≃ g1: {Graph.is_congruent g1 g1}"
  IO.println s!"g1 ≃ g2: {Graph.is_congruent g1 g2}"
  IO.println s!"g1.compact: {g1.compactNodes.toHashMap.toList}"
  IO.println s!"g2.compact: {g2.compactNodes.toHashMap.toList}"
  IO.println s!"g3.compact: {g3.compactNodes.toHashMap.toList}"
  IO.println s!"independent.root: {independent.root.val}"
  IO.println s!"independent: {(independent, independent.root.val)}"
  try
    let gv1 := "lake-test_g2.gv"
    g2.dumpAsDot gv1
    IO.println gv1 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv1]}
    IO.FS.removeFile gv1
    let gv2 := "lake-test_g2-compact.gv"
    g2.compactNodes.dumpAsDot gv2
    IO.println gv2 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv2]}
    IO.FS.removeFile gv2
    let gv3 := "lake-test_independent.gv"
    independent.dumpAsDot gv3
    IO.println gv3 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv3]}
    IO.FS.removeFile gv3
  catch
    | e => IO.println s!"Failed to make a png: {e}"
  IO.println done

end Test_Graph
