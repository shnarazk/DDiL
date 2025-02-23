import TestNumberOfPaths.Basic
import Utils.Debug

open SquareGrid

def main : IO Unit := do
  assert_eq "SquareGrid(1)" (SquareGrid.of 1).numberOfPaths 2
  assert_eq "SquareGrid(2)" (SquareGrid.of 2).numberOfPaths 12
  assert_eq "SquareGrid(3)" (SquareGrid.of 3).numberOfPaths 184
  assert_eq "SquareGrid(4)" (SquareGrid.of 4).numberOfPaths 8_512
  -- assert_eq "SquareGrid(5)" (SquareGrid.of 5).numberOfPaths 1_262_816
  -- assert_eq "SquareGrid(6)" (SquareGrid.of 6).numberOfPaths 565_780_564
  -- 頑張れスーパーコンピューター
  -- assert_eq "SquareGrid(7)" (SquareGrid.of 7).numberOfPaths 789_360_053_252
