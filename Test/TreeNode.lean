import Common.Debug
import Common.DecisionDiagram
import Common.GraphShape
import Common.TreeNode

namespace Test_TreeNode

def f := TreeNode.newConstant false
def t := TreeNode.newConstant true
def n2 := TreeNode.newVar f t 2 |>.assignIndex |>.fst
def n3 := TreeNode.newVar f n2 3 |>.assignIndex |>.fst
def s1_noComment := TreeNode.fromString "{F T}"
def s1_comment1 := TreeNode.fromString "{\"comment\" F T}"
def s1_comment2 := TreeNode.fromString "{  \"comment\"  F T}"
def independent := TreeNode.fromString
  "{  { { {{{T T} {T F}} {{T T} {F F}}}
          {{{T T} {T F}} {{F F} {F F}}} }
        { {{{T T} {T F}} {{T T} {F F}}}
          {{{F F} {F F}} {{F F} {F F}}} } }
      { { {{{T F} {T F}} {{T F} {F F}}}
          {{{T F} {T F}} {{F F} {F F}}} }
        { {{{F F} {F F}} {{F F} {F F}}}
          {{{F F} {F F}} {{F F} {F F}}} } } }"

def run : IO Unit := do
  let (start, done) := LogKind.info.color
  IO.println start
  IO.println "#Test_TreeNode"
  assert_eq "f.shape" (GraphShape.shapeOf f) (0, 1)
  assert_eq "s1nc.shape" (GraphShape.shapeOf s1_noComment) (1, 3)
  assert_eq "congruent s1nc s1c1" (DecisionDiagram.isCongruent s1_noComment s1_comment1) true
  assert_eq "s1c1.shape" (GraphShape.shapeOf s1_comment1) (1, 3)
  assert_eq "congruent s1nc s1c2" (DecisionDiagram.isCongruent s1_noComment s1_comment2) true
  assert_eq "parse w comment2 →shape" (GraphShape.shapeOf s1_comment2) (1, 3)
  assert_eq "s1_nc.isCongruent s1c1" (DecisionDiagram.isCongruent s1_noComment s1_comment1) true
  assert_eq "s1_nc.isCongruent s1c2" (DecisionDiagram.isCongruent s1_noComment s1_comment2) true
  assert_eq "independent      →shape" (GraphShape.shapeOf independent) (6, 127)
  assert_eq "independent.paths" (DecisionDiagram.numberOfSatisfyingPaths independent) 18
  IO.println done

end Test_TreeNode
