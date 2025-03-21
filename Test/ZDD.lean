import Common.Debug
import Graph.Def
import Graph.Serialize
import BDD.Def
import ZDD.Base

namespace Test_ZDD

def or : MergeFunction := MergeFunction.of (· || ·) (some (true, true))

def compaction : IO Unit := do
  IO.println "## compaction"
  return ()

def independent : IO Unit := do
  IO.println "## independent"
  return ()

/-- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println "## apply"
  return ()

def compose : IO Unit := do
  IO.println "## compose"
  return ()

def satisfy : IO Unit := do
  IO.println "## satisfy"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println s!"{beg}{ANSI.bold}#Test_ZDD{fin}{beg}"

  compaction
  independent
  apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_ZDD
