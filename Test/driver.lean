import Test.TreeNode
-- import Test.Node
import Test.Graph
import Test.BDD
import Test.ZDD
import Common.Debug

open ANSI

def main : IO Unit := do
  -- Test_TreeNode.run
  -- Test_Graph.run
  -- Test_BDD.run
  Test_ZDD.run
  IO.println s!"{green}{reverse}done.{reset}"
