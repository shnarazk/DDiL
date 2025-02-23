import TestNumberOfPaths.Basic

open SquareGrid

def main : IO Unit := do
  let g := (Grid.mk : Grid 2)
  IO.println s!"Grid {g.getSize} has {g.numberOfPaths} paths"
