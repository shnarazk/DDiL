class GraphSerialize (γ : Type) where
  dumpAsDot : γ → String → String → IO String
  dumpAsPng : γ → String → String → IO String
