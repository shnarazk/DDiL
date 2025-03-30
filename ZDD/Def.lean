import Common.GraphShape
import Graph.Serialize
import ZDD.Reduce
import ZDD.Apply

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

instance : GraphSerialize ZDD where
  dumpAsDot self path desc := GraphSerialize.dumpAsDot (↑self : Graph) path desc
  dumpAsPng self path desc := GraphSerialize.dumpAsPng (↑self : Graph) path desc
