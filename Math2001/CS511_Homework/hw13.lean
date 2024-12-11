import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 13 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 10.1.5.4
section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : ¬Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  intro h
  dsimp [Int.ModEq] at h
  trivial

example : ¬Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 0, 6
  constructor
  · use 1
    numbers
  · intro h
    dsimp [Int.ModEq] at h
    trivial

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain ⟨k, h1⟩ := h1
  have : y = 5 * k + (x + 1) := by
    rw [← h1]
    ring
  subst y
  dsimp [Int.ModEq] at h2
  conv at h2 => ring
  apply Int.dvd_iff_dvd_of_dvd_sub at h2
  obtain ⟨h1, h2⟩ := h2
  have : 5 ∣ k * 5 := by
    use k
    ring
  apply h2 at this
  trivial

example : ¬Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 0, 1, 2
  constructor
  · numbers
  · constructor <;> numbers

end

/- # Exercise 4 -/

-- Exercise 10.1.5.5
section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : ¬Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [h]

example : ¬AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 0, 3
  constructor
  · use 1
    numbers
  · constructor
    · use 1
      numbers
    · numbers

example : ¬Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, -2
  constructor
  · use 1
    numbers
  · constructor
    · use 0
      numbers
    · dsimp [Int.ModEq]
      trivial

end

/- # Problem 2 -/

-- Exercise 10.1.5.6
example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  intro x
  rfl

example : ¬Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use {1}, {1, 2}
  constructor
  · intro x h
    subst x
    apply Set.mem_insert
  · intro contra
    apply @Set.mem_of_subset_of_mem _ _ _ 2 at contra
    have : 2 ∈ {1, 2} := by
      apply Set.mem_insert_of_mem
      rfl
    apply contra at this
    trivial

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  apply Set.eq_of_subset_of_subset

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  calc
    x ⊆ y := by apply h1
    _ ⊆ z := by apply h2
