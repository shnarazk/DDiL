import Mathlib.Tactic

section proofs

theorem array_element_induction {α : Type} (p : α → Nat) (a : Array α) (h : ∀ x ∈ a, p x < a.size)
    (b : α) (hb : p b < (a.push b).size) :
    ∀ x ∈ a.push b, p x < (a.push b).size := by
  have tr (n : α) {s : Nat} : p n < s → p n < s + 1 := by
    exact Nat.lt_succ_of_lt
  simp [Array.push]
  intro x h'
  rcases h' with h₁ | h₂
  {rcases h x h₁ with h₂ ; exact tr x (h x h₁)}
  {simp [h₂] at * ; exact hb}

theorem le_induction (n : Nat) : ∀ i : Nat, i < n + 1 → i < n ∨ i == n := by
  intro i h
  simp
  exact Nat.lt_succ_iff_lt_or_eq.mp h

theorem array_index_induction {α : Type} (a : Array α) (p : α → Prop) (b : α)
    (h : ∀ i < a.size, match a[i]? with | none => true | some e => p e) (pb : p b) :
    ∀ i < (a.push b).size, match (a.push b)[i]? with | none => true | some e => p e := by
  have {q : Nat → Prop} : (∀ i < (a.push b).size, q i) → (∀ i < (a.push b).size - 1, q i) ∨ (q (a.push b).size) := by
    have : (a.push b).size = a.size + 1 := by simp [Array.push]
    simp [this]
    intro x
    constructor
    { intro j hj
      rcases x j with hj'
      have : j < a.size + 1 := by exact Nat.lt_add_right 1 hj
      exact hj' this }
  intro i h'
  rcases Nat.lt_trichotomy i a.size with h₀ | h' | hp
  { rcases h i h₀ with h₁
    have get₀ : i < a.size → a[i]? = some a[i] := by
      intro h
      exact Array.getElem?_eq_getElem h₀
    rcases get₀ h₀ with get₀
    have get₁ : i < a.size → (a.push b)[i]? = some a[i] := by
      intro h
      exact Array.getElem?_push_lt h₀
    rcases get₁ h₀ with get₁
    simp [get₀, get₁]
    simp [get₀, get₁] at h₁
    exact h₁ }
  { simp [h'] ; exact pb }
  { have : (a.push b).size = a.size + 1 := by exact Array.size_push b
    simp [this] at h'
    have : i ≤ a.size := by exact Nat.le_of_lt_succ h'
    have : ¬a.size < i := by exact Nat.not_lt.mpr this
    contradiction }

instance : LT (Option Nat) where
  lt o₁ o₂ := match o₁ with
    | none => match o₂ with
      | none => false
      | some _ => true
    | some i => match o₂ with
      | none => false
      | some j => i < j

open Option

instance : DecidableLT (Option Nat) :=
  fun o₁ o₂ => by
    induction' o₁ with i
    {
      induction' o₂ with j
      {
        have : ¬(none : Option Nat) < none := by simp [LT.lt]
        exact isFalse this
      }
      {
        have : (none : Option Nat) < some j := by simp [LT.lt]
        exact isTrue this
      }
    }
    {
      induction' o₂ with j
      {
        have : ¬some i < none := by simp [LT.lt]
        exact isFalse this
      }
      {
        if h : i < j
        then
          have : some i < some j := by exact h
          exact isTrue this
        else
          have : ¬some i < some j := by exact h
          exact isFalse this
      }
    }

end proofs
