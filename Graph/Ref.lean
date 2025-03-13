/--
Reference to other node or a constant, having `grounded` and `link`.
There are two constructors: `Ref.bool` and `Ref.to`. -/
structure Ref where
  grounded : Bool
  link : Option Nat
deriving BEq, Hashable

instance : Inhabited Ref where
  default := {grounded := false, link := none}

instance : ToString Ref where
  toString self := match self with
    | {grounded := false, link := none}   => "⊥"
    | {grounded := true , link := none}   => "⊤"
    | {grounded := true , link := some i} => s!"to:{i}"
    | {grounded := false, link := some i} => s!"to:{i}"

def Ref.lt (self other : Ref) : Prop := match self.link, other.link with
  | none  , none   => False
  | none  , some _ => True
  | some _, none   => False
  | some i, some j => i < j

instance : LT Ref where
  lt := Ref.lt

instance DecidableLTRef : DecidableLT Ref
  | {grounded := _, link := none}  , {grounded := _, link := none}    => isFalse not_false
  | {grounded := _, link := none}  , {grounded := _, link := some _}  => isTrue trivial
  | {grounded := _, link := some _}, {grounded := _, link := none}    => isFalse not_false
  | {grounded := _, link := some i}, {grounded := _, link := some j}  =>
      if h : i < j then isTrue h else isFalse h

/-- Ref constructor for boolean values -/
def Ref.bool (b : Bool) : Ref := {grounded := b, link := none}

/-- Ref constructor for node references -/
def Ref.to (n : Nat) : Ref := {grounded := false, link := some n}

-- #eval (Ref.to 3) < (Ref.to 4)

/-- Return `some bool_value` if the reference is constant, `none` otherwise -/
def Ref.asBool (self : Ref) : Option Bool := match self.link with
  | none => some self.grounded
  | some _ => none

/-- Return `true` if it refers to a prior node -/
def Ref.isSmaller (self : Ref) (n : Nat) : Bool := match self.link with
  | none => true
  | some i => i < n

instance : HAdd Ref Nat Ref where
  hAdd r n := match r.link with
    | none => r
    | some i => { r with link := some (i + n) }
