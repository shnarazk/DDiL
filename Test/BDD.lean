import Graph.Basic
import Graph.Serialize
import BDD.Def
import Common.Debug

namespace Test_BDD

def merger : IO Unit := do
  IO.println s!"{ANSI.bold}## merge function: or{ANSI.unbold}"
  assert_eq "true or true" (LiftedBool.or.apply (some true) (some true)) (some true)
  assert_eq "none or true" (LiftedBool.or.apply none (some true)) (some true)
  assert_eq "none or none" (LiftedBool.or.apply none none) none

def compaction : IO Unit := do
  IO.println s!"{ANSI.bold}## compaction{ANSI.unbold}"
  let comp1 : Graph := Graph.fromNodes 2 #[
    {varId := 2, li := Ref.bool true, hi := Ref.bool false},
    {varId := 1, li := Ref.to 0, hi := Ref.to 0} ]
  assert_eq "Graph(compaction-before).shape" (GraphShape.shapeOf comp1) (2, 2)
  let comp2 : BDD := comp1.toBDD
  assert_eq "BDD(compaction-after).shape" (GraphShape.shapeOf comp2) (2, 1)
  try
    IO.println s!"📈 Graph(compaction) → {← comp1.dumpAsPng "_test_bdd_compact-1.png"}"
    IO.println s!"📈 BDD(compaction)   → {← comp2.dumpAsPng "_test_bdd_compact-2.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

def independent : IO Unit := do
  IO.println s!"{ANSI.bold}## independent{ANSI.unbold}"
  -- one of the examples in The Art of Computer Programming
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
  let independent := ind.toBDD
  assert_eq "BDD.independent.shape" (GraphShape.shapeOf independent) (6, 17)
  assert_eq "BDD.independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent) 18
  -- assert_eq "congruence" (independent_bdd.isCongruent independent) true
  try
    IO.println s!"📈 independent → {← independent.dumpAsPng "_test_bdd_indep.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

/-- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println s!"{ANSI.bold}## BDD apply on independent{ANSI.unbold}"
  let x1x3 : BDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool true, hi := Ref.bool false},
      {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
  let x1x2 : BDD := Graph.fromNodes 3 #[
      {varId := 3, li := Ref.bool false, hi := Ref.bool true},
      {varId := 2, li := Ref.bool false, hi := Ref.to 0} ]
    |>.toBDD
  assert_eq "x1x3.shape" (GraphShape.shapeOf x1x3) (3, 2)
  assert_eq "x1x2.shape" (GraphShape.shapeOf x1x2) (3, 2)
  let applied := BDD.apply LiftedBool.or x1x3 x1x2
  -- the output before compaction
  let fig7 : Graph := Graph.fromNodes 3 #[
    {varId := 3, li := Ref.bool true, hi := Ref.bool true},
    {varId := 3, li := Ref.bool true, hi := Ref.bool false},
    {varId := 2, li := Ref.to 1, hi := Ref.to 0},
    {varId := 1, li := Ref.bool true, hi := Ref.to 2} ]
  let fig7_bdd := fig7.toBDD
  assert_eq "x1x3.apply or x1x2 |> shape" (GraphShape.shapeOf applied) (3, 3)
  assert_eq "congruent (x1x3.apply or x1x2) fig7" (DecisionDiagram.isCongruent applied fig7_bdd) true
  try
    IO.println s!"📈 x1x3            → {← x1x3.dumpAsPng     "_test_bdd_apply-1.png"}"
    IO.println s!"📈 x1x2            → {← x1x2.dumpAsPng     "_test_bdd_apply-2.png"}"
    IO.println s!"📈 x1x3.apply.x1x2 → {← applied.dumpAsPng  "_test_bdd_apply-3.png"}"
    IO.println s!"📈 fig7_bdd        → {← fig7_bdd.dumpAsPng "_test_bdd_apply-4.png"}"
    IO.println s!"📈 fig7            → {← fig7.dumpAsPng     "_test_bdd_apply-5.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

def compose : IO Unit := do
  IO.println s!"{ANSI.bold}## BDD compose on the example used in apply{ANSI.unbold}"
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
    IO.println s!"📈 composed1 → {← composed1.dumpAsPng "_test_bdd_compose-1.png"}"
    IO.println s!"📈 composed2 → {← composed2.dumpAsPng "_test_bdd_compose-2.png"}"
  catch e => IO.println s!"Error: {e}"
  return ()

def satisfy : IO Unit := do
  IO.println s!"{ANSI.bold}## satisfy{ANSI.unbold}"
  -- one of the examples in The Art of Computer Programming
  let independent : BDD :=
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
  assert_eq "independent contains [1]   " (independent.contains [1]) true
  assert_eq "independent contains [1, 2]" (independent.contains [1,  2]) false
  assert_eq "independent contains [1,-2]" (independent.contains [1, -2]) true
  assert_eq "independent contains [4,-5]" (independent.contains [4, -5]) true
  assert_eq "independent contains [4, 5]" (independent.contains [4,  5]) false
  -- if ([4, 5] : List Int) ∈ independent then IO.println "ok" else IO.println "ng"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.info.color
  IO.println s!"{beg}{ANSI.bolded "#Test_BDD"}"

  merger
  compaction
  independent
  apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_BDD
