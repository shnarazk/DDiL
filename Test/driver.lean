import Common.Node
import BDD

def f := Node.newConstant false
def t := Node.newConstant true
def n2 := Node.newVar 2 f t 2 |>.assignIndex |>.fst
def n3 := Node.newVar 1 f n2 3 |>.assignIndex |>.fst

def main : IO Unit := do
  IO.println "Hello, World!"
  IO.println s!"Node: {n3}"
