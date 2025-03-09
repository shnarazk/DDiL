import Test.TreeNode
-- import Test.Node
import Test.Graph
import Test.BDD

def main : IO Unit := do
  Test_TreeNode.run
  -- Test_Node.run
  Test_Graph.run
  Test_BDD.run
  IO.println "done."
