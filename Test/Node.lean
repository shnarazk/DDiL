import Common.Node

namespace Test_Node

def f := Node.mk 1 (Ref.bool false) (Ref.bool true)
-- def t := Node.newConstant true
-- def n2 := Node.newNode 2 0 1
-- def n3 := Node.newNode 1 1 3

def test : IO Unit := do
  IO.println s!"Node f: {f}"
  -- IO.println s!"Node: {n3}"
  IO.println "test tree"

end Test_Node
