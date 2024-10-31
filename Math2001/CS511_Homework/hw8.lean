import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 8 Lean Exercises -/

/- # Exercise 3 -/

-- Lecture Slides 18, pg. 25
example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  obtain ⟨z, hz⟩ := h;
  intro x y
  rw [← hz x]
  exact hz y

-- Lecture Slides 29 Part III, pg. 8
example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intro h v w
  obtain ⟨x, hx⟩ := h;
  rw [← hx v]
  exact hx w

/- # Exercise 4 -/

-- Exercise 5.3.6.9
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain h | h := le_or_lt t 4
  · right
    addarith [h]
  · left
    exact h

-- Example 6.1.2
example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp [Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw [hx]
      ring
    · left
      use x + 1
      rw [hx]
      ring

-- Example 6.1.6
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ k * 2 ≥ k ^ 2 * 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra

/- # Problem 2 -/

-- Exercise 5.3.6.12
example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a * a
  conv => ring
  extra

-- Exercise 6.1.7.2
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · conv => ring
  · have ha' : 0 ≤ 1 + a := by addarith [ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + (k + 1) * a + (k * a ^ 2) := by ring
      _ ≥ 1 + (k + 1) * a := by extra

-- Exercise 6.1.7.3
example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · left
    use 0
    ring
  · obtain IH | IH := IH
    · right
      obtain ⟨m, hm⟩ := IH
      have hm' : 5 ^ k = 8 * m + 1 := by addarith [hm]
      conv => lhs; ring
      rw [hm']
      use 5 * m
      ring
    · left
      obtain ⟨m, hm⟩ := IH
      have hm' : 5 ^ k = 8 * m + 5 := by addarith [hm]
      conv => lhs; ring
      rw [hm']
      use 5 * m + 3
      ring
