import Common.Debug
import Common.TreeNode

namespace Test_TreeNode

def f := TreeNode.newConstant false
def t := TreeNode.newConstant true
def n2 := TreeNode.newVar f t 2 |>.assignIndex |>.fst
def n3 := TreeNode.newVar f n2 3 |>.assignIndex |>.fst
def s1 := TreeNode.ofString "{F T}"
def independent := TreeNode.ofString
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
  IO.println s!"independent: {independent}"
  IO.println done

end Test_TreeNode
