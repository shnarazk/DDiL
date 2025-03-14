class GraphShape (γ : Type) where
  numberOfVars : γ → Nat
  numberOfNodes : γ → Nat
  shapeOf : γ → (Nat × Nat) := fun g ↦ (numberOfVars g, numberOfNodes g)
