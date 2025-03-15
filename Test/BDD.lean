import Graph.Def
import Graph.Serialize
import BDD.Def

namespace Test_BDD

/-- an extended boolean function that can take wildecards
- `true || *` => `true`
- `* || true` => `true` -/
def or : MergeFunction := MergeFunction.of (· || ·) (some (true, true))

def merger : IO Unit := do
  IO.println "## merge function: or"
  assert_eq "true or true" (or.apply (some true) (some true)) (some true)
  assert_eq "none or true" (or.apply none (some true)) (some true)
  assert_eq "none or none" (or.apply none none) none

def compaction : IO Unit := do
  IO.println "## compaction"
  let comp1 : Graph := Graph.fromNodes 2 #[
      {varId := 2, li := Ref.bool true, hi := Ref.bool false},
      {varId := 1, li := Ref.to 0, hi := Ref.to 0} ]
  assert_eq "Graph(compaction-before).shape" (GraphShape.shapeOf comp1) (2, 2)
  let comp2 : BDD := comp1.toBDD
  assert_eq "BDD(compaction-after).shape" (GraphShape.shapeOf comp2) (2, 1)
  try
    let file1 ← comp1.dumpAsPng "_test_bdd_compaction-before.png"
    IO.println s!"📈 Graph(compaction) was dumped as: {file1}"
    let file2 ← comp2.dumpAsPng "_test_bdd_compaction-after.png"
    IO.println s!"📈 BDD(compaction) was dumped as: {file2}"
  catch e => IO.println s!"Error: {e}"
  return ()

def independent : IO Unit := do
  IO.println "## independent"
  -- one of the examples in The Art of Computer Programming
  let independent_bdd : BDD :=
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
  assert_eq "BDD.independent.shape" (GraphShape.shapeOf independent_bdd) (6, 17)
  assert_eq "BDD.independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent_bdd) 18
  try
    let file ← independent_bdd.dumpAsPng "_test_bdd1.png"
    IO.println s!"📈 independent_bdd was dumped as: {file}"
  catch e => IO.println s!"Error: {e}"
  return ()

/-- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println "## BDD apply on independent"
  let x1x3 : BDD := Graph.fromNodes 3 #[
        {varId := 3, li := Ref.bool true, hi := Ref.bool false},
        {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
  let x1x2 : BDD := Graph.fromNodes 3 #[
        {varId := 3, li := Ref.bool false, hi := Ref.bool true},
        {varId := 2, li := Ref.bool false, hi := Ref.to 0} ]
    |>.toBDD
  IO.println s!"x1x3: {GraphShape.shapeOf x1x3}"
  IO.println s!"x1x2: {GraphShape.shapeOf x1x2}"
  let applied := BDD.apply or x1x3 x1x2
  -- the output before compaction
  let fig7 : Graph := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool true, hi := Ref.bool true},
      {varId := 3, li := Ref.bool true, hi := Ref.bool false},
      {varId := 2, li := Ref.to 1, hi := Ref.to 0},
      {varId := 1, li := Ref.bool true, hi := Ref.to 2} ]
  let fig7_bdd := fig7.toBDD
  assert_eq "x1x3.apply or x1x2 |> shape" (GraphShape.shapeOf applied) (3, 3)
  try
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
  catch e => IO.println s!"Error: {e}"
  return ()

def compose : IO Unit := do
  IO.println "## BDD compose on the example used in apply"
  let x1x3 : BDD := Graph.fromNodes 3 #[
        {varId := 3, li := Ref.bool true, hi := Ref.bool false},
        {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
  let x1x2 : BDD := Graph.fromNodes 3 #[
        {varId := 3, li := Ref.bool false, hi := Ref.bool true},
        {varId := 2, li := Ref.bool false, hi := Ref.to 0} ]
    |>.toBDD
  -- This replace x1x3 with x1x2 completely.
  let composed1 := BDD.compose x1x3 x1x2 1
  assert_eq "(compose x1x3 x1x2 1).shape" (GraphShape.shapeOf composed1) (3, 2)
  -- This operation combine x1x2 into x1x3 under var1
  let composed2 := BDD.compose x1x3 x1x2 2
  assert_eq "(compose x1x3 x1x2 2).shape" (GraphShape.shapeOf composed2) (3, 2)
  try
    let file1 ← (↑composed1 : Graph).dumpAsPng "_test_bdd_compose1.png"
    IO.println s!"📈 composed1 was dumped as: {file1}"
    let file2 ← (↑composed2 : Graph).dumpAsPng "_test_bdd_compose2.png"
    IO.println s!"📈 composed2 was dumped as: {file2}"
  catch e => IO.println s!"Error: {e}"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println beg
  IO.println "#Test_BDD"

  merger
  compaction
  independent
  apply
  compose

  IO.println fin
  return ()

end Test_BDD
