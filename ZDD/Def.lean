import Common.GraphShape
import Graph.Serialize
import ZDD.Reduce
import ZDD.Apply

instance : GraphShape ZDD where
  numberOfVars self := GraphShape.numberOfVars (↑self : Graph)
  numberOfNodes self := GraphShape.numberOfNodes (↑self : Graph)
  shapeOf self := GraphShape.shapeOf (↑self : Graph)

-- instance : DecisionDiagram ZDD where
--   numberOfSatisfyingPaths := ZDD.numSatisfies
--   apply := ZDD.apply
--   compose := ZDD.compose
--   isCongruent := ZDD.isCongruent
--   contains := ZDD.contains

-- instance : Membership (List Int) BDD where
--   mem b l := (b.contains l : Prop)

instance : GraphSerialize ZDD where
  dumpAsDot self path desc := GraphSerialize.dumpAsDot (↑self : Graph) path desc
  dumpAsPng self path desc := GraphSerialize.dumpAsPng (↑self : Graph) path desc
