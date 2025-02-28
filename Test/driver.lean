-- import Common.Node
import Common.TreeNode
import BDD

def f := TreeNode.newConstant false
def t := TreeNode.newConstant true
def n2 := TreeNode.newVar 2 f t 2 |>.assignIndex |>.fst
def n3 := TreeNode.newVar 1 f n2 3 |>.assignIndex |>.fst

def main : IO Unit := do
  IO.println "Hello, World!"
  IO.println s!"Node: {n3}"
