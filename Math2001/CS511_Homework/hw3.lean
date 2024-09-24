import Library.Basic
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 3 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 2.3.6.2
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  · rw [h]
    ring
  · rw [h]
    ring

-- Exercise 2.3.6.3
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  · rw [h]
    ring
  · rw [h]
    ring

-- Exercise 2.3.6.4
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h | h := h
  · rw [h]
    ring
  · rw [h]
    ring

/- # Exercise 4 -/

-- Exercise 2.3.6.12
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hx | hx := hx
  · apply ne_of_lt
    calc
      2 * x ≤ 2 * 1 := by rel [hx]
      _ < 3 := by numbers
  · apply ne_of_gt
    calc
      3 < 2 * 2 := by numbers
      _ ≤ 2 * x := by rel [hx]

-- Exercise 2.4.5.1
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨H1, H2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [H1, H2]
    _ ≤ 4 := by numbers

-- Exercise 2.4.5.6
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · calc
      x = 2 * (x + y) - (x + 2 * y) := by ring
      _ = 2 * 5 - 7 := by rw [h1, h2]
      _ = 3 := by numbers
  · calc
      y = x + 2 * y - (x + y) := by ring
      _ = 7 - 5 := by rw [h1, h2]
      _ = 2 := by numbers

/- # Problem 2 -/

-- Exercise 2.3.6.10
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : (t ^ 2 + 0) * (t - 1) = 0 := by
    calc
      (t ^ 2 + 0) * (t - 1) = t ^ 3 - t ^ 2 := by ring
      _ = t ^ 2 - t ^ 2 := by rw [ht]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  · have h3 : t ^ 2 = 0 := by addarith [h2]
    right
    cancel 2 at h3
  · left
    addarith [h2]

-- Exercise 2.3.6.14
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hm | hm := hm
  · apply ne_of_lt
    calc
      m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [hm]
      _ < 46 := by numbers
  · apply ne_of_gt
    calc
      46 < 6 ^ 2 + 4 * 6 := by numbers
      _ ≤ m ^ 2 + 4 * m := by rel [hm]

-- Exercise 2.4.5.7
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : (a - 1) * (b + 0) = 0 := by
    calc
      (a - 1) * (b + 0) = a * b - b := by ring
      _ = b - b := by rw [h2]
      _ = 0 := by ring
  have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  obtain h4 | h4 := h4
  · right
    constructor
    · addarith [h4]
    · rw [← h2, h1]
      addarith [h4]
  · left
    constructor
    · rw [← h1, h2]
      addarith [h4]
    · addarith [h4]
