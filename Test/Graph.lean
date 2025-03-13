import Common.Debug
import Common.DecisionDiagram
import Graph.Graph

namespace Test_Node

def f := Node.mk 1 (Ref.bool false) (Ref.bool true)
def t := Node.mk 2 (Ref.bool true) (Ref.bool true)
-- def t := Node.newConstant true
-- def n2 := Node.newNode 2 0 1
-- def n3 := Node.newNode 1 1 3

def run : IO Unit := do
  IO.println s!"Node f: {f}"
  IO.println s!"Node t: {t}"
  -- IO.println s!"Node: {n3}"
  IO.println "test tree"

end Test_Node

namespace Test_Graph

def g₀ : Graph := default
def g₁ : Graph := { (default : Graph) with
    numVars := 3
    validVarIds := by decide
  }
def g₁₁ := Graph.forVars 3
def g₂ : Graph := g₁.addNode' 1 (Ref.bool true) (Ref.bool false) |>.fst
def g₃ : Graph := TreeNode.fromString "{{{T F} {F F}} {{T F} {F F}}}" |> Graph.fromTreeNode

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

def run : IO Unit := do
  let (start, done) := LogKind.warn.color
  IO.println start
  IO.println "#Test_Graph"
  IO.println s!"Graph g₀: {g₀}"
  IO.println s!"Graph g₁: {g₁}"
  assert_eq "Graph.forVars 3" g₁₁ g₁
  IO.println s!"Graph g₂: {g₂}"
  assert_eq "GraphShape.ofShape g₃" (GraphShape.shapeOf g₃) (3, 7)
  assert_eq "GraphShape.OfShape g₂" (GraphShape.shapeOf g₂) (3, 1)
  assert_eq "GraphShape.ofShape independent" (GraphShape.shapeOf independent) (6, 63)
  assert_eq "independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent) 18
  try
    let file ← independent.dumpAsPng "lake-test_independent.png"
    IO.println s!"📈 independent was dumped as: {file}"
  catch e => IO.println s!"Error: {e}"
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
