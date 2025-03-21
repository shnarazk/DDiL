import Common.Debug
import Common.DecisionDiagram
-- import Graph.Def
import Graph.Serialize

namespace Test_Node

def run : IO Unit := do
  let f := Node.mk 1 (Ref.bool false) (Ref.bool true)
  let t := Node.mk 2 (Ref.bool true) (Ref.bool true)
  -- def t := Node.newConstant true
  -- def n2 := Node.newNode 2 0 1
  -- def n3 := Node.newNode 1 1 3
  IO.println s!"Node f: {f}"
  IO.println s!"Node t: {t}"
  -- IO.println s!"Node: {n3}"
  IO.println "test tree"

end Test_Node

namespace Test_Graph

def g₀ : Graph := default
def g₁ : Graph := {(default : Graph) with numVars := 3, validVarIds := by decide}
def g₁₁ := Graph.forVars 3
def g₂ : Graph := g₁.addNode' 1 (Ref.bool true) (Ref.bool false) |>.fst
def g₃ : Graph := TreeNode.fromString "{{{T F} {F F}} {{T F} {F F}}}" |> Graph.fromTreeNode

def independent : IO Unit := do
  let tree := TreeNode.fromString
    "{  { { {{{T T} {T F}} {{T T} {F F}}}
            {{{T T} {T F}} {{F F} {F F}}} }
          { {{{T T} {T F}} {{T T} {F F}}}
            {{{F F} {F F}} {{F F} {F F}}} } }
        { { {{{T F} {T F}} {{T F} {F F}}}
            {{{T F} {T F}} {{F F} {F F}}} }
          { {{{F F} {F F}} {{F F} {F F}}}
            {{{F F} {F F}} {{F F} {F F}}} } } }"
  let g := Graph.fromTreeNode tree
  -- assert_eq "GraphShape.ofShape independent" (GraphShape.shapeOf g) (6, 63)
  -- assert_eq "independent.paths" (DecisionDiagram.numberOfSatisfyingPaths g) 18
  try
    IO.println s!"📈 independent → {← g.dumpAsPng "_test_independent.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

def run : IO Unit := do
  let (start, done) := LogKind.warn.color
  IO.println start
  IO.println s!"{start}{ANSI.bold}#Test_Graph{done}{start}"

  IO.println s!"Graph g₀: {g₀}"
  IO.println s!"Graph g₁: {g₁}"
  assert_eq "Graph.forVars 3" g₁₁ g₁
  IO.println s!"Graph g₂: {g₂}"
  assert_eq "GraphShape.ofShape g₃" (GraphShape.shapeOf g₃) (3, 7)
  assert_eq "GraphShape.OfShape g₂" (GraphShape.shapeOf g₂) (3, 1)

  independent

  IO.println done

end Test_Graph
