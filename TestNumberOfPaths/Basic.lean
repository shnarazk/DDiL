/- Decision Diagram Library in Lean4
- test example2: the number of paths in size n square grid
-/
import Std
import Common.Combinators

open Std

namespace SquareGrid

variable {size : Nat}

structure SquareGrid (size : Nat)

def SquareGrid.of (size : Nat) : SquareGrid size := (SquareGrid.mk : SquareGrid size)

def SquareGrid.getSize (_ : SquareGrid size) : Nat := size

def SquareGrid.goal (_ : SquareGrid size) : Nat := size.succ * size.succ - 1
def SquareGrid.start (_ : SquareGrid size) : Nat := 0

def SquareGrid.goalPosition (_ : SquareGrid size) : Nat × Nat := (size, size)
def SquareGrid.startPosition (_ : SquareGrid size) : Nat × Nat := (0, 0)

def SquareGrid.mask (_ : SquareGrid size) (p : Nat × Nat) : Option (Nat × Nat) :=
  if p.1 <= size ∧ p.2 <= size then some p else none

example : (SquareGrid.of 2).mask (4, 0) = none := rfl

def SquareGrid.position (_ : SquareGrid size) (id : Nat) : Nat × Nat := (id / size.succ, id % size.succ)

def SquareGrid.toId (_ : SquareGrid size) (p : Nat × Nat) : Nat := p.1 * size.succ + p.2

/-
-- I don't like to import mathlib just for proving it.
lemma from_to_eq_id (n : Nat) : @fromDim2 size (@toDim2 size n) = n := by
  simp [toDim2, fromDim2]
  exact Nat.div_add_mod' n size
-/

def SquareGrid.neighborsOf (s : SquareGrid size) (n : Nat) : Array Nat :=
  let p := s.position n
  [
    p.1 > 0    |> toSome (p.1.pred, p.2     ),
    p.1 < size |> toSome (p.1.succ, p.2     ),
    p.2 > 0    |> toSome (p.1,      p.2.pred),
    p.2 < size |> toSome (p.1,      p.2.succ),
  ]
    |>.filterMap id
    |>.map (s.toId ·)
    |>.toArray

--  0  1  2  3
--  4  5  6  7
--  8  9 10 11
-- 12 13 14 15
example : (SquareGrid.of 3).position 4 = (1, 0) := rfl
example : ((SquareGrid.of 3).neighborsOf 4).insertionSort = #[0, 5, 8].insertionSort := rfl

/--
This is just a simple expansion process; we don't need to keep track of the searched space.
-/
partial def expand (s : SquareGrid size) (path : Array Nat) : Nat :=
  if path.back? = some s.goal
  then 1
  else
    s.neighborsOf path.back!
      |>.filter (!path.contains ·)
      |>.foldl (fun acc n => acc + expand s (path.push n)) 0

def SquareGrid.countNumberOfPathsNaively (s : SquareGrid size) : Nat :=
  expand s #[0]

def SquareGrid.numberOfPaths (s : SquareGrid size) : Nat :=
  s.countNumberOfPathsNaively

end SquareGrid
