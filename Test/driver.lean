import Test.TreeNode
import Test.Node
import Test.Graph

def main : IO Unit := do
  Test_TreeNode.test
  Test_Node.test
  Test_Graph.run
  IO.println "done."
