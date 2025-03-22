import Common.Debug
import Common.LiftedBool

namespace Test_LiftedBool

def merger : IO Unit := do
  assert_eq "true or true" (LiftedBool.or.apply (some true) (some true)) (some true)
  assert_eq "none or true" (LiftedBool.or.apply none (some true)) (some true)
  assert_eq "none or none" (LiftedBool.or.apply none none) none

def run : IO Unit := do
  let (beg, fin) := LogKind.info.color
  IO.println s!"{beg}{ANSI.bolded "ListedBool"}"
  merger
  IO.println fin
  return ()

  end Test_LiftedBool
