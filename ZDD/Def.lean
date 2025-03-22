import Common.GraphShape
import ZDD.Reduce

instance : GraphShape ZDD where
  numberOfVars self := GraphShape.numberOfVars (↑self : Graph)
  numberOfNodes self := GraphShape.numberOfNodes (↑self : Graph)
  shapeOf self := GraphShape.shapeOf (↑self : Graph)

-- instance : DecisionDiagram BDD where
--   numberOfSatisfyingPaths := BDD.numSatisfies
--   apply := BDD.apply
--   compose := BDD.compose
--   isCongruent := BDD.isCongruent
--   contains := BDD.contains

-- instance : Membership (List Int) BDD where
--   mem b l := (b.contains l : Prop)
