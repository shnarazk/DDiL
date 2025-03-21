import Common.DecisionDiagram
import BDD.Base
import BDD.Reduce
import BDD.Apply
import BDD.Compose
import BDD.Congruence
import BDD.Satisfy

instance : GraphShape BDD where
  numberOfVars self := GraphShape.numberOfVars (↑self : Graph)
  numberOfNodes self := GraphShape.numberOfNodes (↑self : Graph)
  shapeOf self := GraphShape.shapeOf (↑self : Graph)

instance : DecisionDiagram BDD where
  numberOfSatisfyingPaths := BDD.numSatisfies
  apply := BDD.apply
  compose := BDD.compose
  isCongruent := BDD.isCongruent
  contains := BDD.contains
