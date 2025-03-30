import Common.Debug
import Graph.Basic
import Graph.Reorder
import Graph.Serialize
import BDD.Def
import ZDD.Def
import ZDD.Reduce
import ZDD.Conversion

open Std

namespace Test_ZDD

private def ind : Graph :=
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
--  IO.println s!"📈 ind       → {← ind.dumpAsPng "_test_zdd_trim-1.png" "ind"}"

def png {α : Type} [GraphSerialize α] (g : α) (label filename : String)
    (description : String := "")
    : IO Unit := do
  let description := if description == "" then label else s!"{label}: {description}"
  let val ← GraphSerialize.dumpAsPng g filename description
  IO.println s!"📈 {label} → {val}"
  return ()

def insert : IO Unit := do
  IO.println s!"{ANSI.bolded "## insert"}"
  /-
  let b14 : BDD := Graph.fromNodes 4 #[
      {varId := 4, li := Ref.bool true, hi := Ref.bool false},
      {varId := 1, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
  let i14 := ZDD_reduce.insert b14.toGraph
  IO.println s!"b14i: {i14}"
  let g14 := Graph.reorderNodes 4 i14 (Ref.last b14.toGraph.nodes)
  IO.println s!"g14: {g14}"
  try
    IO.println s!"📈 i14   → {← b14.dumpAsPng "_test_zdd_insert-1.png"}"
    IO.println s!"📈 g14   → {← g14.dumpAsPng "_test_zdd_insert-2.png"}"
  catch e => IO.println s!"Error: {e}"
  -/
  /-
  let b25 : BDD := Graph.fromNodes 5 #[
      {varId := 5, li := Ref.bool false, hi := Ref.bool true},
      {varId := 2, li := Ref.bool true, hi := Ref.to 0} ]
    |>.toBDD
    |>.startFromOne
  IO.println s!"b25: {b25}"
  let i25 := ZDD_reduce.insert b25.toGraph
  IO.println s!"i25: {i25}"
  let g25 := Graph.reorderNodes 5 i25 (Ref.last b25.toGraph.nodes)
  IO.println s!"g25: {g25}"

  try
    IO.println s!"📈 b25   → {← b25.dumpAsPng "_test_zdd_insert-3.png"}"
    IO.println s!"📈 g25   → {← g25.dumpAsPng "_test_zdd_insert-4.png"}"
  catch e => IO.println s!"Error: {e}"
  -/
  let ind_inserted : Array Node := ZDD_conversion.insert ind
  IO.println s!"ind_inserted: {ind_inserted}"
  let ind_reordered := Graph.reorderNodes 6 ind_inserted (Ref.last ind.nodes)
  IO.println s!"ind_reordered: {ind_reordered}"
  try
    png (Graph.ofNodes ind_inserted) "ind_inserted"  "_test_zdd_insert-3.png" "ind→insert"
    png ind_reordered                "ind_reordered" "_test_zdd_insert-4.png" "ind→insert→reorder"
  catch e => IO.println s!"Error: {e}"
  return ()

def trim : IO Unit := do
  IO.println s!"{ANSI.bolded "## trim"}"
  let ind_ins  : Array Node := ZDD_conversion.insert ind
  let ind_pp   : Graph      := Graph.reorderNodes 6 ind_ins (Ref.last ind.nodes)
  let ind_trim : Graph      := ZDD_reduce.trim ind_pp.nodes
    |>.fst
    |> Node.compact
    |> Graph.ofNodes
  -- IO.println s!"ind_trim: {ind_trim}"
  let indb      : BDD        := ind.toBDD
  let indb_ins  : Array Node := ZDD_conversion.insert indb.toGraph
  let indb_pp   : Graph      := Graph.reorderNodes 6 indb_ins (Ref.last indb.nodes)
  let indb_trim : Graph      := ZDD_reduce.trim indb_pp.nodes
    |>.fst
    |> Node.compact
    |> Graph.ofNodes
  -- IO.println s!"indb_trim: {indb_trim}"
  try
    png ind      "ind (TreeNode)"   "_test_zdd_trim-1.png" "TreeNode"
    png ind_pp   "ind_pp (Graph)"   "_test_zdd_trim-2.png" "ind→insert+reorder"
    png ind_trim "ind_trim (Graph)" "_test_zdd_trim-3.png" "ind→trim"
    png indb "indb (BDD)" "_test_zdd_trim-4.png" "ind→BDD"
    png indb_pp "indb_pp (Graph)" "_test_zdd_trim-5.png" "ind→BDD→insert+reorder"
    png indb_trim "indb_trim (Graph)" "_test_zdd_trim-6.png" "ind→BDD→insert+reorder→trim"
  catch e => IO.println s!"Error: {e}"
  return ()

def reduce : IO Unit := do
  IO.println s!"{ANSI.bolded "## reduce independent toBDD toZDD"}"
  let indB : BDD := ind.toBDD
  let indZ : ZDD := indB.toZDD
  assert_eq "ZDD.independent.shape" (GraphShape.shapeOf indZ) (6, 9)
  assert_eq "ZDD.independent.paths" indZ.numSatisfies 18
  -- assert_eq "ZDD.independent.paths" (DecisionDiagram.numberOfSatisfyingPaths indZ) 18
  -- assert_eq "congruence" (independent_bdd.isCongruent independent) true
  try
    -- IO.println s!"ind (Graph) → {ind}"
    -- IO.println s!"ind (BDD)   → {indB}"
    -- IO.println s!"ind (ZDD)   → {indZ}"
    png ind  "ind (Graph)" "_test_zdd_reduce-1.png" "Tree → Graph"
    png indB "ind (BDD)"   "_test_zdd_reduce-2.png" "Tree → BDD"
    png indZ "ind (ZDD)"   "_test_zdd_reduce-3.png" "Tree → BDD → ZDD"
  catch e => IO.println s!"Error: {e}"
  return ()

def compaction : IO Unit := do
  IO.println s!"{ANSI.bolded "## compaction"}"
  return ()

/- /- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println s!"{ANSI.bolded "## ZDD apply"}"
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
    png x1x3     "x1x3 (ZDD)"     "_test_zdd_apply-1.png"
    png x1x2     "x1x2 (ZDD)"     "_test_zdd_apply-2.png"
    png applied  "applied (ZDD)"  "_test_zdd_apply-3.png" "apply x1x3 x1x2"
    png fig7     "fig7 (Graph)"   "_test_zdd_apply-5.png" "hand crafted version"
    png fig7_zdd "fig7_zdd (ZDD)" "_test_zdd_apply-4.png" "fig7.toBDD.toZDD"
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

  -- insert
  trim
  reduce
  -- compaction
  -- apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_ZDD
