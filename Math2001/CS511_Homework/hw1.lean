import Library.Basic
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 1 Lean Exercises -/

-- Exercise 3: Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = ((3 * w + 1) - 1) / 3 := by ring
    _ = (4 - 1) / 3 := by rw [h1]
    _ = 1 := by ring

-- Exercise 4: Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3
      = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Problem 2: Section 1.3.11, Exercise 7
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a = a + 2 * b + 3 * c - (2 * b + 3 * c) := by ring
    _ = 7 - (2 * b + 3 * c) := by rw [h1]
    _ = 7 - (2 * (b + 2 * c) - c) := by ring
    _ = 7 - (2 * 3 - 1) := by rw [h2, h3]
    _ = 2 := by ring
