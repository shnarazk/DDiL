import Common.Debug
import Graph.Basic
import Graph.Reorder
import Graph.Serialize
import BDD.Def
import ZDD.Def
import ZDD.Reduce
import ZDD.Conversion

namespace Test_ZDD

def insert : IO Unit := do
  IO.println s!"{ANSI.bolded "## insert"}"
  let x1_4 : BDD := Graph.fromNodes 4 #[
    {varId := 4, li := Ref.bool true, hi := Ref.bool false},
    {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
  |>.toBDD
  let _r := Ref.last x1_4.toGraph.nodes
  let x14 := ZDD_reduce.insert x1_4.toGraph
    -- |>(fun nodes ↦ Graph.compact (Graph.fromNodes 4 (dbg? "insert" nodes)) (some r))
  IO.println s!"x14: {x14}"
  let z14 := Graph.reorderNodes 4 x14 (Ref.last x1_4.toGraph.nodes)
  IO.println s!"z14: {z14}"

  let x2_5 : BDD := Graph.fromNodes 5 #[
    {varId := 5, li := Ref.bool false, hi := Ref.bool true},
    {varId := 2, li := Ref.bool true, hi := Ref.to 0} ]
  |>.toBDD
  let x2_5 := x2_5.startFromOne
  let _r2 := Ref.last x2_5.toGraph.nodes
  let x25 := ZDD_reduce.insert x2_5.toGraph
    -- |>(fun nodes ↦ Graph.compact (Graph.fromNodes 4 (dbg? "insert" nodes)) (some r))
  IO.println s!"x25: {x25}"
  let z25 := Graph.reorderNodes 5 x25 (Ref.last x2_5.toGraph.nodes)
  IO.println s!"z25: {z25}"
  try
    IO.println s!"📈 x1_4   → {← x1_4.dumpAsPng "_test_zdd_insert-1.png"}"
    IO.println s!"📈 z14    → {← z14.dumpAsPng  "_test_zdd_insert-2.png"}"
    IO.println s!"📈 x2_5   → {← x2_5.dumpAsPng "_test_zdd_insert-3.png"}"
    IO.println s!"📈 z25    → {← z25.dumpAsPng  "_test_zdd_insert-4.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

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
  let independent := ind.toBDD.toZDD
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

/- /- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println s!"{ANSI.bolded "## ZDD apply on independent"}"
  let x1x3 : ZDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool true, hi := Ref.bool false},
      {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
    |>.toZDD
  let x1x2 : ZDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool false, hi := Ref.bool true},
      {varId := 2, li := Ref.bool false, hi := Ref.to 0} ]
    |>.toBDD
    |>.toZDD
  assert_eq "x1x3.shape" (GraphShape.shapeOf x1x3) (3, 2)
  assert_eq "x1x2.shape" (GraphShape.shapeOf x1x2) (3, 2)
  let applied := ZDD.apply LiftedBool.or x1x3 x1x2
  -- the output before compaction
  let fig7 : Graph := Graph.fromNodes 3 #[
    {varId := 3, li := Ref.bool true, hi := Ref.bool true},
    {varId := 3, li := Ref.bool true, hi := Ref.bool false},
    {varId := 2, li := Ref.to 1, hi := Ref.to 0},
    {varId := 1, li := Ref.bool true, hi := Ref.to 2} ]
  let fig7_zdd := fig7.toBDD.toZDD
  assert_eq "x1x3.apply or x1x2 |> shape" (GraphShape.shapeOf applied) (3, 3)
  -- assert_eq "congruent (x1x3.apply or x1x2) fig7" (DecisionDiagram.isCongruent applied fig7_zdd) true
  try
    IO.println s!"📈 x1x3            → {← x1x3.dumpAsPng     "_test_zdd_apply-1.png"}"
    IO.println s!"📈 x1x2            → {← x1x2.dumpAsPng     "_test_zdd_apply-2.png"}"
    IO.println s!"📈 x1x3.apply.x1x2 → {← applied.dumpAsPng  "_test_zdd_apply-3.png"}"
    IO.println s!"📈 fig7_zdd        → {← fig7_zdd.dumpAsPng "_test_zdd_apply-4.png"}"
    IO.println s!"📈 fig7            → {← fig7.dumpAsPng     "_test_zdd_apply-5.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()
-/

 def compose : IO Unit := do
  IO.println s!"{ANSI.bolded "## compose"}"
  return ()

def satisfy : IO Unit := do
  IO.println s!"{ANSI.bolded "## satisfy"}"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println s!"{beg}{ANSI.bolded "#Test_ZDD"}"

  insert
  reduce
  compaction
  -- apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_ZDD
