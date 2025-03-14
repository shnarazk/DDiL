import Common.Combinators
import Common.GraphShape
import Common.DecisionDiagram
import Graph.Def
import BDD.Reduce

open Std

namespace BDD_compose

variable (g : Graph)

def step (g : Graph) (_v1l _v1h v2 : Ref) : Ref :=
  -- Perform restrictions
  -- Apply operation ITE
  v2

end BDD_compose

def BDD.compose (a _b : BDD) (_varIndex : Nat) : BDD :=
  a
