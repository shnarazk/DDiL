
/-- Asserts that two values `a` and `b` are equal. -/
def assert_eq {T : Type} [BEq T] [ToString T] (s : String) (a b : T) : IO Unit := do
  if a == b then
    IO.println s!"✅ Assertion: {s} == {b}"
  else
    IO.println s!"🆖 Assertion: {s} == {b}"
