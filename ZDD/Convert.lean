import Common.TreeNode
import ZDD.Basic
import ZDD.Operations

/--
  Converts a `TreeNode` to a `ZDD`.

  This function takes a `TreeNode` and produces a corresponding `ZDD`.
  The current implementation returns the default value for `ZDD`.
-/
def convertFromTreeNode (t : TreeNode) : ZDD :=
  (default : ZDD)
