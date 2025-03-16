import Common.Combinators
import Common.GraphShape

structure MergeFunction where
  private fn : Bool → Bool → Bool
  private unit : Option (Bool × Bool)

def MergeFunction.of (fn : Bool → Bool → Bool) (unit : Option (Bool × Bool) := none) : MergeFunction :=
  ⟨fn, unit⟩

def MergeFunction.apply (f : MergeFunction) (a b : Option Bool) : Option Bool := match a, b with
  | none,   none   => none
  | none,   some a => if let some (i, o) := f.unit then (a == i).map o else none
  | some a, none   => if let some (i, o) := f.unit then (a == i).map o else none
  | some a, some b => f.fn a b |> some

  instance : Coe MergeFunction (Bool → Bool → Bool) where
  coe f := f.fn

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  numberOfSatisfyingPaths : α → Nat
  apply : MergeFunction→ α → α → α
  /-- Combine two diagrams into one as follows
  f1 \ xi=f2
  So this a sort of substitution. -/
  compose : α → α → Nat → α
  /--
  Check if two diagrams are congruent.
  Two diagrams are congruent if they have the same satisfying paths. -/
  isCongruent : α → α → Bool
