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

def SquareGrid.goal (_ : SquareGrid size) : Nat := (size + 1) * (size + 1) - 1
def SquareGrid.start (_ : SquareGrid size) : Nat := 0

def SquareGrid.goalPosition (_ : SquareGrid size) : Nat × Nat := (size, size)
def SquareGrid.startPosition (_ : SquareGrid size) : Nat × Nat := (0, 0)

def SquareGrid.mask (_ : SquareGrid size) (p : Nat × Nat) : Option (Nat × Nat) :=
  if p.1 <= size ∧ p.2 <= size then some p else none

example : (SquareGrid.of 2).mask (4, 0) = none := by simp [SquareGrid.mask]

def SquareGrid.position (_ : SquareGrid size) (id : Nat) : Nat × Nat := (id / (size + 1), id % (size + 1))
def SquareGrid.toId (_ : SquareGrid size) (p : Nat × Nat) : Nat := p.1 * (size + 1) + p.2

def SquareGrid.neighbors (s : SquareGrid size) (n : Nat) : Array Nat :=
  let p := s.position n
  [
    if p.1 > 0 then some (p.1 - 1, p.2) else none,
    if p.1 < size then some (p.1 + 1, p.2) else none,
    if p.2 > 0 then some (p.1, p.2 - 1) else none,
    if p.2 < size then some (p.1, p.2 + 1) else none
  ]
    |>.filterMap id
    |>.map (s.toId ·)
    |>.toArray

--  0  1  2  3
--  4  5  6  7
--  8  9 10 11
-- 12 13 14 15
example : (SquareGrid.of 3).position 4 = (1, 0) := rfl
example : ((SquareGrid.of 3).neighbors 4).insertionSort = #[0, 5, 8].insertionSort := rfl

/--
This is just a simple expansion process; we don't need to keep track of the searched space.
-/
partial def expand (s : SquareGrid size) (path : Array Nat) : Nat :=
  if path.back? = some s.goal
  then 1
  else
    s.neighbors path.back!
      |>.filter (!path.contains ·)
      |>.foldl (fun acc n => acc + expand s (path.push n)) 0

def SquareGrid.countNumberOfPathsNaively (s : SquareGrid size) : Nat :=
  expand s #[0]

def SquareGrid.numberOfPaths (s : SquareGrid size) : Nat :=
  s.countNumberOfPathsNaively

end SquareGrid
