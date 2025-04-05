import Std.Data.HashSet
import Common.Debug
import Graph.Ref
import Mathlib.Tactic

open Std

/--
Node representation for graph, having `varId`, `li`, and `hi`.
This has an order that matches the occurence order of the nodes in the `Graph.nodes`. -/
structure Node where
  varId : Nat
  li    : Ref
  hi    : Ref
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

instance decidableLTNode : DecidableLT Node
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

instance arrayRefOrder : LT ((Array Node) × Ref) where
  lt o₁ o₂ :=
    let (a₁, r₁) := o₁
    let (a₂, r₂) := o₂
    match r₁ with
    | {grounded := b₁, link := none} => match r₂ with
      | {grounded := b₂, link := none}  => b₁ < b₂
      | {grounded := _, link := some _} => true
    | {grounded := _, link := some n} => match r₂ with
      | {grounded := _, link := none}   => false
      | {grounded := _, link := some m} => a₁[n]! < a₂[m]!

open Ref in
instance : DecidableLT ((Array Node) × Ref) :=
  fun o₁ o₂ ↦ by
    rcases o₁ with ⟨a₁, r₁⟩
    rcases r₁ with ⟨b₁, l₁⟩
    rcases o₂ with ⟨a₂, r₂⟩
    rcases r₂ with ⟨b₂, l₂⟩
    induction' l₁ with m
    {
      induction' l₂ with n
      {simp [LT.lt] at * ; exact instDecidableAnd}
      {simp [LT.lt] at * ; exact instDecidableTrue}
    }
    {
      induction' l₂ with n
      {simp [LT.lt] at * ; exact instDecidableFalse}
      {simp [arrayRefOrder] at * ; exact decidableLTNode a₁[m]! a₂[n]!}
    }

namespace Node_compact

private partial
def usedNodes (nodes : Array Node) (root : Ref)
    (mapping : HashSet Ref := HashSet.empty)
    : HashSet Ref :=
  if let some (i) := root.link then
    if mapping.contains root then
      mapping
    else
      let node : Node := nodes[i]!
      usedNodes nodes node.li (mapping.insert root) |> usedNodes nodes node.hi
  else
    mapping

private
def compact (nodes : Array Node) (root : Ref := Ref.last nodes) : Array Node :=
  let used : Array Ref := usedNodes nodes root |>.toArray |>.insertionSort (· < ·)
  let mapping : HashMap Ref Ref := used.zipIdx.map (fun (n, i) ↦ (n, Ref.to i))
    |>.toList
    |>HashMap.ofList
  used.map
    (if let some i := ·.link then
        let node := nodes[i]!
        {node with li := mapping.getD node.li node.li, hi := mapping.getD node.hi node.hi}
      else
        (default : Node) )

end Node_compact

def Node.compact (nodes : Array Node) (root : Ref := Ref.last nodes) : Array Node :=
  Node_compact.compact nodes root
