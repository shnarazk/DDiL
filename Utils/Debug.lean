
/-- Asserts that two values `a` and `b` are equal. -/
def assert_eq {T : Type} [BEq T] [ToString T] (a b : T) : IO Unit := do
  if a == b then
    IO.println s!"Assertion: {a} == {b} passed"
  else
    IO.println s!"Assertion: {a} == {b} failed"
