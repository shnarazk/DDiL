/-- Constant combinator -/
def cI {α : Type} (a : α) : Unit -> α :=
  fun _ ↦ a

def mapToOption {α : Type} (p : Prop) [Decidable p] (f : Unit -> α) : Option α :=
  if p then some (f ()) else none

example : mapToOption (1 = 1) (cI 42) = some 42 := rfl

def toSome {α : Type} (t : α) (p : Prop) [Decidable p] : Option α :=
  if p then some t else none

example : ((1 = 1) |> toSome 42) = some 42 := rfl
