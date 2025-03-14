
class GraphSerialize (γ : Type) where
  dumpAsDot : γ → String → IO String
  dumpAsPng : γ → String → IO String
