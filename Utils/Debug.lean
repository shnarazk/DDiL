
/-- Asserts that two values `a` and `b` are equal. -/
def assert_eq {α : Type} [BEq α] [ToString α] (s : String) (a b : α) : IO Unit := do
  if a == b then
    IO.println s!"✅ Assertion: {s} == {b}"
  else
    IO.println s!"🆖 Assertion: {s} == {b}"
