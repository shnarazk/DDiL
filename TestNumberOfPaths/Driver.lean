import TestNumberOfPaths.Basic
import Utils.Debug

open SquareGrid

def main : IO Unit := do
  let g2 := (SquareGrid.mk : SquareGrid 2)
  IO.println s!"SquareGrid({g2.getSize}) has {g2.numberOfPaths} paths"
  assert_eq g2.numberOfPaths 6
  assert_eq (SquareGrid.of 1).numberOfPaths 2
  assert_eq (SquareGrid.of 2).numberOfPaths 12
  assert_eq (SquareGrid.of 3).numberOfPaths 184
  assert_eq (SquareGrid.of 4).numberOfPaths 8_512
  assert_eq (SquareGrid.of 5).numberOfPaths 1_262_816
  -- assert_eq (SquareGrid.of 6).numberOfPaths 565_780_564
  -- 頑張れスーパーコンピューター
  -- assert_eq (SquareGrid.of 7).numberOfPaths 789_360_053_252
