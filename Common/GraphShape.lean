class GraphShape (γ : Type) where
  numberOfVars : γ → Nat
  numberOfNodes : γ → Nat
  /-- Returns the shape of the graph as a pair of the number of variables and nodes. -/
  shapeOf : γ → (Nat × Nat) := fun g ↦ (numberOfVars g, numberOfNodes g)
