import Common.Debug
import Common.TreeNode

namespace Test_TreeNode

def f := TreeNode.newConstant false
def t := TreeNode.newConstant true
def n2 := TreeNode.newVar 2 f t 2 |>.assignIndex |>.fst
def n3 := TreeNode.newVar 1 f n2 3 |>.assignIndex |>.fst

def independent := TreeNode.ofString
  "{ 1
      { 2
        { 3
          {4 {5 {6 T T} {6 T F}} {5 {6 T T} {6 F F}}}
          {4 {5 {6 T T} {6 T F}} {5 {6 F F} {6 F F}}} }
        { 3
          {4 {5 {6 T T} {6 T F}} {5 {6 T T} {6 F F}}}
          {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}} } }
      { 2
        { 3
          {4 {5 {6 T F} {6 T F}} {5 {6 T F} {6 F F}}}
          {4 {5 {6 T F} {6 T F}} {5 {6 F F} {6 F F}}} }
        { 3
          {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}}
          {4 {5 {6 F F} {6 F F}} {5 {6 F F} {6 F F}}} } }
    }"

def test : IO Unit := do
  let (start, done) := LogKind.info.color
  IO.println start
  IO.println s!"TreeNode: {f}"
  IO.println s!"independent: {independent}"
  IO.println done

end Test_TreeNode
