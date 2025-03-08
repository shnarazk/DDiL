import Common.Debug
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

def test : IO Unit := do
  let (start, done) := LogKind.info.color
  IO.println start
  IO.println s!"TreeNode: {f}"
  IO.println s!"parse w/o comment: {s1_noComment}"
  IO.println s!"parse w comment1: {s1_comment1}"
  IO.println s!"parse w comment2: {s1_comment2}"
  IO.println s!"independent: {independent}"
  IO.println done

end Test_TreeNode
