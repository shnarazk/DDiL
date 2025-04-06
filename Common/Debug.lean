import Std.Data.HashMap

inductive LogKind : Type where
  | info  : LogKind
  | log   : LogKind
  | warn  : LogKind
  | error : LogKind

namespace ANSI

def red     : String := "\x1B[031m"
def green   : String := "\x1B[032m"
def blue    : String := "\x1B[034m"
def magenta : String := "\x1B[035m"
def cyan    : String := "\x1B[036m"
def reset   : String := "\x1B[000m"
def revert  : String := "\x1B[1A\x1B[1G\x1B[1K"
def reverse : String := "\x1B[007m"
def bold    : String := "\x1B[001m"
def unbold  : String := "\x1B[022m"

def bolded {α : Type} [ToString α] (s : α) : String :=
  s!"{bold}{s}{unbold}"

end ANSI

open ANSI in
def LogKind.color (kind : LogKind) : String × String := match kind with
  | .info  => (cyan , reset)
  | .log   => (green, reset)
  | .warn  => (blue , reset)
  | .error => (red  , reset)

def dbg {α : Type} (label : String) (a : α) (kind : LogKind := LogKind.log) : α :=
  let colors := LogKind.color kind
  dbgTrace s!"{colors.fst}{label}{colors.snd}" (fun _ ↦ a)

/-- Display debug info without the value -/
def dbg! {α : Type} (label : String) (a : α) (kind : LogKind := LogKind.log) : α :=
  let colors := LogKind.color kind
  dbgTrace s!"{colors.fst}{label}{colors.snd}" (fun _ ↦ a)

/-- Display debug info with the value -/
def dbg? {α : Type} [ToString α] (label : String) (a : α) (kind : LogKind := LogKind.log) : α :=
  let colors := LogKind.color kind
  dbgTrace s!"{colors.fst}{label}: {a}{colors.snd}" (fun _ ↦ a)

  open ANSI in
  /-- Asserts that two values `a` and `b` are equal. -/
  def assert_eq {α : Type} [BEq α] [ToString α] (s : String) (a b : α) : IO Unit := do
    if a == b then
      IO.println s!"✅ {s} == {b}"
    else
      let (beg, fin) := LogKind.error.color
      IO.println s!"{beg}🆖 {s} → {a} ≠ {b}{fin}"

/--
Format string with left padding. -/
def paddingLeft {α : Type} [ToString α] (t : α) (w : Nat := 8) : String :=
  let s := ToString.toString t
  List.range (max (w - s.length) 0) |>.map (fun _ ↦ " ") |> String.join |>.append s

-- #eval paddingLeft "Hello" 8

instance {α : Type} [ToString α] : ToString (Std.HashMap Nat α) where
  toString h := h.toList.mergeSort (·.fst < ·.fst)
    |>.map (fun (k, v) ↦ s!"\n{paddingLeft k 4}: {paddingLeft v 8}")
    |> String.join

-- #eval s!"{(Std.HashMap.emptyWithCapacity : Std.HashMap Nat String) |>.insert 2 "two" |>.insert 5 "five"}"
