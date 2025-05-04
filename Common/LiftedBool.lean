import Common.Combinators

namespace LiftedBool

structure UnaryFunction where
  private fn : Bool → Bool

def UnaryFunction.of (fn : Bool → Bool) : UnaryFunction :=
  ⟨fn⟩

def UnaryFunction.apply (f : UnaryFunction) (b : Option Bool) : Option Bool := match b with
  | none   => none
  | some b => f.fn b |> some

instance : Coe UnaryFunction (Bool → Bool) where
  coe f := f.fn

def not : UnaryFunction := UnaryFunction.of (! ·)

structure BinaryFunction where
  private fn : Bool → Bool → Bool
  private unit : Option (Bool × Bool)

def BinaryFunction.of (fn : Bool → Bool → Bool) (unit : Option (Bool × Bool) := none) : BinaryFunction :=
  ⟨fn, unit⟩

def BinaryFunction.apply (f : BinaryFunction) (a b : Option Bool) : Option Bool := match a, b with
  | none,   none   => none
  | none,   some a => if let some (i, o) := f.unit then (a == i).map o else none
  | some a, none   => if let some (i, o) := f.unit then (a == i).map o else none
  | some a, some b => f.fn a b |> some

  instance : Coe BinaryFunction (Bool → Bool → Bool) where
  coe f := f.fn

/-- an extended boolean function that can take wildcards
- `falld && *` => `false`
- `* && false` => `false` -/
def and : BinaryFunction := BinaryFunction.of (· && ·) (some (false, false))

/-- an extended boolean function that can take wildcards
- `true || *` => `true`
- `* || true` => `true` -/
def or : BinaryFunction := BinaryFunction.of (· || ·) (some (true, true))

end LiftedBool
