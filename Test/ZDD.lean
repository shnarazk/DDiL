import Common.Debug
import Graph.Basic
import Graph.Serialize
import BDD.Def
import ZDD.Basic

namespace Test_ZDD

def compaction : IO Unit := do
  IO.println s!"{ANSI.bolded "## compaction"}"
  return ()

def independent : IO Unit := do
  IO.println s!"{ANSI.bolded "## independent"}"
  return ()

/-- the apply example used in the paper -/
def apply : IO Unit := do
  IO.println s!"{ANSI.bolded "## apply"}"
  return ()

def compose : IO Unit := do
  IO.println s!"{ANSI.bolded "## compose"}"
  return ()

def satisfy : IO Unit := do
  IO.println s!"{ANSI.bolded "## satisfy"}"
  return ()

def run : IO Unit := do
  let (beg, fin) := LogKind.error.color
  IO.println s!"{beg}{ANSI.bolded "#Test_ZDD"}"

  compaction
  independent
  apply
  compose
  satisfy

  IO.println fin
  return ()

end Test_ZDD
