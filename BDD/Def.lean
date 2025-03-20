import Common.DecisionDiagram
import BDD.Base
import BDD.Reduce
import BDD.Apply
import BDD.Compose
import BDD.Satisfy

instance : GraphShape BDD where
  numberOfVars self := GraphShape.numberOfVars (↑self : Graph)
  numberOfNodes self := GraphShape.numberOfNodes (↑self : Graph)
  shapeOf self := GraphShape.shapeOf (↑self : Graph)

instance : DecisionDiagram BDD where
  numberOfSatisfyingPaths b := b.numSatisfies
  apply := BDD.apply
  compose := BDD.compose
  isCongruent (self other : BDD) := DecisionDiagram.isCongruent (↑self : Graph) (↑other : Graph)
  contains self path := self.isSatisfiedBy path
