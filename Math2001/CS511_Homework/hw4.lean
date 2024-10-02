import AutograderLib
import Library.Basic
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 4 Lean Exercises -/

/- # Exercise 3 -/

-- Example 2.5.5
@[autograded 2]
theorem exercise3a : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

-- Example 2.5.6
@[autograded 2]
theorem exercise3b (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1), a
  ring

-- Example 2.5.7
@[autograded 2]
theorem exercise3c {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  · calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring

/- # Exercise 4 -/

-- Exercise 3.1.10.3
@[autograded 2]
theorem exercise4a {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Even, Odd] at *
  obtain ⟨kn, hkn⟩ := hn
  obtain ⟨km, hkm⟩ := hm
  use km + kn
  rw [hkn, hkm]
  ring

-- Exercise 4.1.10.1
@[autograded 2]
theorem exercise4b {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by ring

-- Example 4.1.3
@[autograded 2]
theorem exercise4c {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain h | h := h ((a + b) / 2)
  · calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [h]
      _ = a := by ring
  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [h]
      _ = b := by ring

/- # Problem 2 -/

-- Exercise 3.2.9.2
@[autograded 2]
theorem problem2a : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

-- Exercise 3.2.9.5
@[autograded 2]
theorem problem2b {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  rw [hk]
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  ring

-- Exercise 3.2.9.6
@[autograded 2]
theorem problem2c {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use a ^ 3 * b
  rw [hb, ha]
  ring
