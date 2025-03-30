import Common.DecisionDiagram
import Graph.Serialize
import BDD.Basic
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

instance : GraphSerialize BDD where
  dumpAsDot self path desc := GraphSerialize.dumpAsDot (↑self : Graph) path desc
  dumpAsPng self path desc := GraphSerialize.dumpAsPng (↑self : Graph) path desc

instance : Membership (List Int) BDD where
  mem b l := (b.contains l : Prop)
