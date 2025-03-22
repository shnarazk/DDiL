import Common.Debug
import Graph.Basic
import Graph.Serialize
-- import BDD.Def
import ZDD.Def

namespace Test_ZDD

def reduce : IO Unit := do
  IO.println s!"{ANSI.bolded "## reduce"}"
  let ind : Graph :=
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
  let independent := ind.toZDD
  -- assert_eq "ZDD.independent.shape" (GraphShape.shapeOf independent) (6, 17)
  -- assert_eq "ZDD.independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent) 18
  -- assert_eq "congruence" (independent_bdd.isCongruent independent) true
  try
    IO.println s!"📈 independent → {← independent.dumpAsPng "_test_zdd_reduce.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

def compaction : IO Unit := do
  IO.println s!"{ANSI.bolded "## compaction"}"
  return ()

/-- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println s!"{ANSI.bolded "## apply"}"
  return ()

def compose : IO Unit := do
  IO.println s!"{ANSI.bolded "## compose"}"
  return ()

def satisfy : IO Unit := do
  IO.println s!"{ANSI.bolded "## satisfy"}"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println s!"{beg}{ANSI.bolded "#Test_ZDD"}"

  reduce
  compaction
  apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_ZDD
