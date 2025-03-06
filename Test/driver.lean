import Test.TreeNode
import Test.Node
-- import Test.Graph
-- import Test.BDD

def main : IO Unit := do
  Test_TreeNode.test
  Test_Node.test
  -- Test_Graph.run
  -- Test_BDD.run
  IO.println "done."
