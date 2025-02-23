/- Decision Diagram Library in Lean4
- test example1: the number of paths in size n square grid
-/
-- import Init.Data.Nat.Basic

namespace SquareGrid

variable {size : Nat}

structure Grid (size : Nat)

-- #check (Grid.mk : Grid 3)
--
def Grid.getSize (_ : Grid size) : Nat := size

def Grid.mask (_ : Grid size) (p : Nat × Nat) : Option (Nat × Nat) :=
  if p.1 < size ∧ p.2 < size then some p else none

example : (Grid.mk : Grid 2).mask (4, 0) = none := by simp [Grid.mask]

def Grid.position (_ : Grid size) (id : Nat) : Nat × Nat := (id / size, id % size)

def Grid.numberOfPaths (_ : Grid size) : Nat := 0

end SquareGrid
