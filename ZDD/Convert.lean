import Common.TreeNode
import ZDD.Basic
import ZDD.Operations

/--
  Converts a `TreeNode` to a `ZDD`.

  This function takes a `TreeNode` and produces a corresponding `ZDD`.
  The current implementation returns the default value for `ZDD`.
-/
def convertFromTreeNode (t : TreeNode) (mgr : ZDDManager := default) : ZDD × ZDDManager :=
  match t with
  | .isFalse  => (ZDD.terminal0, mgr)
  | .isTrue   => (ZDD.terminal1, mgr)
  | .node l h vi =>
    let (z1, mgr) := convertFromTreeNode l mgr
    let (z2, mgr) := convertFromTreeNode h mgr
    makeNode mgr vi z1 z2

instance : Coe TreeNode ZDD where
  coe t := convertFromTreeNode t |>.fst
