import Common.DecisionDiagram
import Graph.Base
import Graph.Congruence

instance : DecisionDiagram Graph where
  numberOfSatisfyingPaths (g : Graph) := g.numSatisfies
  apply (_f : MergeFunction) (g _ : Graph) : Graph := g
  compose (self _other : Graph) (_varId : Nat) : Graph := self
  isCongruent (self other : Graph) : Bool := self.isCongruent other
