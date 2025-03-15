import Graph.Def
import Graph.Serialize
import BDD.Def

namespace Test_BDD

def compaction1 := Graph.fromNodes 2 #[
    {varId := 2, li := Ref.bool true, hi := Ref.bool false},
    {varId := 1, li := Ref.to 0, hi := Ref.to 0} ]

/-- one of the examples in The Art of Computer Programming -/
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

/-- 1st term of the apply example used in the paper -/
def x1x3 : BDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool true, hi := Ref.bool false},
      {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
  |>.toBDD
/-- 2nd term of the apply example used in the paper -/
def x1x2 : BDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool false, hi := Ref.bool true},
      {varId := 2, li := Ref.bool false, hi := Ref.to 0} ]
  |>.toBDD
/-- an extended boolean function that can take wildecards
- `true || *` => `true`
- `* || true` => `true` -/
def or : MergeFunction := MergeFunction.of (· || ·) (some (true, true))
-- the output before compaction
def fig7 : Graph := Graph.fromNodes 3 #[
    {varId := 3, li := Ref.bool true, hi := Ref.bool true},
    {varId := 3, li := Ref.bool true, hi := Ref.bool false},
    {varId := 2, li := Ref.to 1, hi := Ref.to 0},
    {varId := 1, li := Ref.bool true, hi := Ref.to 2} ]

def applied := BDD.apply or x1x3 x1x2
/-- This replace x1x3 with x1x2 completely. -/
def composed1 := BDD.compose x1x3 x1x2 1
/-- This operation combine x1x2 into x1x3 under var1 -/
def composed2 := BDD.compose x1x3 x1x2 2

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println beg
  IO.println "#Test_BDD"
  assert_eq "compaction1.shape" (GraphShape.shapeOf compaction1) (1, 3)
  assert_eq "BDD.independent.shape" (GraphShape.shapeOf independent_bdd) (6, 17)
  assert_eq "BDD.independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent_bdd) 18
  -- IO.println s!"x1x3: {GraphShape.shapeOf x1x3}"
  -- IO.println s!"x1x2: {GraphShape.shapeOf x1x2}"
  assert_eq "true or true" (or.apply (some true) (some true)) (some true)
  assert_eq "none or true" (or.apply none (some true)) (some true)
  assert_eq "none or none" (or.apply none none) none
  assert_eq "x1x3.apply or x1x2 |> shape" (GraphShape.shapeOf applied) (3, 3)
  assert_eq "compose x1x3 x1x2 at 1 |> shape" (GraphShape.shapeOf composed1) (3, 3)
  assert_eq "compose x1x2 x1x3 at 2 |> shape" (GraphShape.shapeOf composed2) (3, 3)
  let fig7_bdd := fig7.toBDD
  -- IO.println s!"bdd1.reduce: {bdd1.reduce.toHashMap.toList}"
  -- IO.println s!"bdd2: {bdd2.toHashMap.toList}"
  -- IO.println s!"bdd2.reduce: {bdd2.reduce.toHashMap.toList}"
  -- IO.println s!"BDD.congruent g1 ≃ g1: {Graph.is_congruent g1 g1}"
  -- IO.println s!"BDD.congruent g1 ≃ g2: {Graph.is_congruent g1 g2}"
  -- if let some message ← independent.reduce.toGraph.dumpAsPng "lake-test_independent-bdd.png"
  --   then IO.println message
  try
    let file ← independent_bdd.dumpAsPng "_test_bdd1.png"
    IO.println s!"📈 independent_bdd was dumped as: {file}"
    let file1 ← compaction1.dumpAsPng "_test_compaction1.png"
    IO.println s!"📈 compaction1 was dumped as: {file1}"
    let file2 ← (↑x1x3 : Graph).dumpAsPng "_test_x1x3.png"
    IO.println s!"📈 x1x3 was dumped as: {file2}"
    let file3 ← (↑x1x2 : Graph).dumpAsPng "_test_x1x2.png"
    IO.println s!"📈 x1x2 was dumped as: {file3}"
    let file4 ← (↑ applied : Graph).dumpAsPng "_test_apply.png"
    IO.println s!"📈 x1x3.apply.x1x2 was dumped as: {file4}"
    let file5 ← (↑fig7_bdd : Graph).dumpAsPng "_test_fig7_bdd.png"
    IO.println s!"📈 fig7_bdd was dumped as: {file5}"
    let file7 ← (↑fig7 : Graph).dumpAsPng "_test_fig7.png"
    IO.println s!"📈 fig7 was dumped as: {file7}"
    let file8 ← (↑composed1 : Graph).dumpAsPng "_test_composed1_bdd.png"
    IO.println s!"📈 composed1 was dumped as: {file8}"
    let file9 ← (↑composed2 : Graph).dumpAsPng "_test_composed2_bdd.png"
    IO.println s!"📈 composed2 was dumped as: {file9}"
  catch e => IO.println s!"Error: {e}"
  IO.println fin
  return ()

end Test_BDD
