
/-- Asserts that two values `a` and `b` are equal. -/
def assert_eq {α : Type} [BEq α] [ToString α] (s : String) (a b : α) : IO Unit := do
  if a == b then
    IO.println s!"✅ Assertion: {s} == {b}"
  else
    IO.println s!"🆖 Assertion: {s} == {b}"

inductive LogKind : Type where
| log : LogKind
| warn : LogKind
| error : LogKind

namespace Debug

def red     : String := "\x1B[001m\x1B[031m"
def green   : String := "\x1B[001m\x1B[032m"
def blue    : String := "\x1B[001m\x1B[034m"
def magenta : String := "\x1B[001m\x1B[035m"
def cyan    : String := "\x1B[001m\x1B[036m"
def reset   : String := "\x1B[000m"
def revert  : String := "\x1B[1A\x1B[1G\x1B[1K"
def reverse : String := "\x1B[001m\x1B[07m"

end Debug

open Debug in
def LogKind.color (kind : LogKind) : String × String := match kind with
  | .log => (green, reset)
  | .warn => (blue, reset)
  | .error => (red, reset)

def dbg {α : Type} (label : String) (a : α) (kind : LogKind := LogKind.log) : α :=
  let colors := LogKind.color kind
  dbgTrace s!"{colors.fst}{label}{colors.snd}" (fun _ ↦ a)
