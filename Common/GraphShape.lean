
class GraphShape (γ : Type) where
  numberOfVars : γ → Nat
  numberOfNodes : γ → Nat
  shapeOf : γ → (Nat × Nat) := fun g ↦ (numberOfVars g, numberOfNodes g)

/-
structure A

def A.numberOfVars (_ : A) : Nat := 3
def A.numberOfNodes (_ : A) : Nat := 5

instance : GraphShape A where
  numberOfVars := A.numberOfVars
  numberOfNodes := A.numberOfNodes

 #eval A.mk.numberOfVars
-/
