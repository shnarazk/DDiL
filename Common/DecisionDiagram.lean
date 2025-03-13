import Common.GraphShape

structure MergeFunction where
  fn : Bool → Bool → Bool
  unit : Option Bool

def MergeFunction.of (fn : Bool → Bool → Bool) (unit : Option Bool := none) : MergeFunction :=
  ⟨fn, unit⟩

def MergeFunction.apply : MergeFunction → Option Bool → Option Bool → Option Bool
  | _, none,   none   => none
  | _, none,   a      => if a == true then some true else some false
  | _, a,      none   => if a == true then some true else some false
  | f, some a, some b => f.fn a b |> some

instance : Coe MergeFunction (Bool → Bool → Bool) where
  coe f := f.fn

/--
Interface for decision diagram built from `Node`.
Note: since diagrams are not trees, traversing them is not efficient.
So we need some caching mechanism in data structures representing diagrams. -/
class DecisionDiagram (α : Type) [BEq α] [GraphShape α] where
  numberOfSatisfyingPaths : α → Nat
  apply : MergeFunction→ α → α → α
  /-- Combine two diagrams into one -/
  compose : α → α → Nat → α
