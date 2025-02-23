/- Decision Diagram Library in Lean4
- test example2: the number of paths in size n square grid
-/
import Std
open Std

namespace SquareGrid

variable {size : Nat}

structure SquareGrid (size : Nat)

def SquareGrid.of (size : Nat) : SquareGrid size := (SquareGrid.mk : SquareGrid size)

def SquareGrid.getSize (_ : SquareGrid size) : Nat := size

def SquareGrid.mask (_ : SquareGrid size) (p : Nat × Nat) : Option (Nat × Nat) :=
  if p.1 < size ∧ p.2 < size then some p else none

example : (SquareGrid.of 2).mask (4, 0) = none := by simp [SquareGrid.mask]

def SquareGrid.position (_ : SquareGrid size) (id : Nat) : Nat × Nat := (id / size, id % size)

def SquareGrid.countNumberOfPathsNaively (_ : SquareGrid size) : Nat :=
  let bag : HashSet (Array Nat) := HashSet.empty
  bag.size

def SquareGrid.numberOfPaths (s : SquareGrid size) : Nat :=
  s.countNumberOfPathsNaively

end SquareGrid
