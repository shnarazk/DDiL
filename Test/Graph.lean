import Common.Debug
-- import Common.Graph
import Common.Node

namespace Test_Graph

def g₀ : Graph := default
def g₁ : Graph := { (default : Graph) with
    numVars := 3
    validVarIds := by decide
  }
def g₁₁ := Graph.forVars 3
def g₂ : Graph := g₁.addNode 1 (Ref.bool true) (Ref.bool false) |>.fst

def independent_tree := TreeNode.fromString
  "{  { { {{{T T} {T F}} {{T T} {F F}}}
          {{{T T} {T F}} {{F F} {F F}}} }
        { {{{T T} {T F}} {{T T} {F F}}}
          {{{F F} {F F}} {{F F} {F F}}} } }
      { { {{{T F} {T F}} {{T F} {F F}}}
          {{{T F} {T F}} {{F F} {F F}}} }
        { {{{F F} {F F}} {{F F} {F F}}}
          {{{F F} {F F}} {{F F} {F F}}} } } }"

def independent := Graph.fromTreeNode independent_tree

-- def g2 : Graph := {
--   nodes := #[
--      .isFalse,
--      .isTrue,
--      .node 1 3 4,
--      .node 2 0 0,
--      .node 2 1 0],
--   root := Fin.ofNat' 5 2,
--   filled := by exact Nat.instNeZeroSucc
-- }

-- def g3 : Graph := {
--   nodes := #[
--      .isFalse,
--      .isTrue,
--      .node 1 3 4,
--      .node 2 0 0,
--      .node 2 1 0,
--      .node 2 0 0,
--      .node 2 1 1],
--   root := Fin.ofNat' 7 2,
--   filled := by exact Nat.instNeZeroSucc
-- }

def run : IO Unit := do
  let (start, done) := LogKind.warn.color
  IO.println start
  IO.println s!"Graph g₀: {g₀}"
  IO.println s!"Graph g₁: {g₁}"
  IO.println s!"Graph g₁₁: {g₁₁}"
  IO.println s!"Graph g₂: {g₂}"
  IO.println s!"GraphShape.numberOfVars g₂: {GraphShape.numberOfVars g₂}"
  IO.println s!"GraphShape.numberOfNodes g₂: {GraphShape.numberOfNodes g₂}"
  IO.println s!"independent: {independent}"
  IO.println s!"GraphShape.ofShape independent: {GraphShape.shapeOf independent}"
  -- IO.println s!"Graph: {(g1, 3)}"
  -- IO.println s!"Graph.toHashMap: {g1.toHashMap.toList}"
  -- IO.println s!"Graph.toHashSet: {g1.toHashSet.toList}"
  -- IO.println s!"g1 ≃ g1: {Graph.is_congruent g1 g1}"
  -- IO.println s!"g1 ≃ g2: {Graph.is_congruent g1 g2}"
  -- IO.println s!"g1.compact: {g1.compactNodes.toHashMap.toList}"
  -- IO.println s!"g2.compact: {g2.compactNodes.toHashMap.toList}"
  -- IO.println s!"g3.compact: {g3.compactNodes.toHashMap.toList}"
  -- IO.println s!"independent.root: {independent.root.val}"
  -- IO.println s!"independent: {(independent, independent.root.val)}"
  -- try
  --   let gv1 := "lake-test_g2.gv"
  --   g2.dumpAsDot gv1
  --   IO.println gv1 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv1]}
  --   IO.FS.removeFile gv1
  --   let gv2 := "lake-test_g2-compact.gv"
  --   g2.compactNodes.dumpAsDot gv2
  --   IO.println gv2 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv2]}
  --   IO.FS.removeFile gv2
  --   let gv3 := "lake-test_independent.gv"
  --   independent.dumpAsDot gv3
  --   IO.println gv3 <* IO.Process.run { cmd := "dot", args := #["-T", "png", "-O", gv3]}
  --   IO.FS.removeFile gv3
  -- catch
  --   | e => IO.println s!"Failed to make a png: {e}"
  IO.println done

end Test_Graph
