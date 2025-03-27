import Common.Debug
import Graph.Ref

/--
Node representation for graph, having `varId`, `li`, and `hi`.
This has an order that matches the occurence order of the nodes in the `Graph.nodes`. -/
structure Node where
  varId : Nat
  li : Ref
  hi : Ref
deriving BEq, Hashable

instance : Inhabited Node where
  default := {varId := 0, li := default, hi := default}

instance : ToString Node where
  toString self :=
    let li := toString self.li
    let hi := toString self.hi
    if li == hi
    then s!"Node(var:{self.varId} ↦ {li})"
    else s!"Node(var:{self.varId}, li:{self.li}, hi:{self.hi})"

instance : ToString (Array Node) where
  toString a := a.zipIdx.map (fun (n, i) ↦ s!"\n{paddingLeft i 4}: {n}") |>.toList |> String.join

/- FIXME: implement `decidable eq` -/
def Node.lt (a b : Node) : Prop :=
  a.varId > b.varId ∨ (a.varId == b.varId ∧ (a.li < b.li ∨ (a.li == b.li ∧ a.hi < b.hi)))

/- This order matches the occurence order of the nodes in the `Graph.nodes`. -/
instance : LT Node where
  lt := Node.lt

instance DecidableLTNode : DecidableLT Node
  | a, b =>
    if h : a.varId > b.varId ∨ (a.varId == b.varId ∧ (a.li < b.li ∨ (a.li == b.li ∧ a.hi < b.hi)))
    then isTrue h
    else isFalse h

def Node.validRef (self : Node) (pos : Nat) : Bool :=
  match self.li.link, self.hi.link with
    | some l, some h => l < pos ∧ h < pos
    | some l, none   => l < pos
    | none  , some h => h < pos
    | none  , none   => true

/-- Return `some bool_value` if both references is a same constant, `none` otherwise -/
def Node.asBool (self : Node) : Option Bool := match self.li.asBool, self.hi.asBool with
  | some l, some h => if l == h then some l else none
  | _, _ => none

def Node.append_nodes (self other : Array Node) (offset : Nat := self.size) : Array Node :=
  self.append <| other.map (fun n ↦ {n with li := n.li + offset, hi := n.hi + offset})

-- #eval append_nodes #[(default : Node), default] #[{(default : Node) with li := Ref.to 0}]
