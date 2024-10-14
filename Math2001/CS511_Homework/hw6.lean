import AutograderLib
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ModEq.Defs
import Library.Theory.ParityModular
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 6 Lean Exercises -/

/- # Exercise 3 -/

--# Exercise 3.4.5.6
@[autograded 3]
theorem exercise_3a (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases hn : n % 2
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^ 2 + 3 * 0 + 7 [ZMOD 2] := by rel [hn]
      _ = 3 * 2 + 1 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by rel [hn]
      _ = 7 * 2 + 1 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra

--# Exercise 3.4.5.7
@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  · calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
      _ ≡ 0 [ZMOD 5] := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
      _ ≡ 1 [ZMOD 5] := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 6 * 5 + 2 := by numbers
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 48 * 5 + 3 := by numbers
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 204 * 5 + 4 := by numbers
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]

/- # Exercise 4 -/

--# Exercise 4.4.6.2
@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have hc : 0 ^ 2 ≡ 4 [ZMOD 5] := by
      calc
        0 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at hc -- contradiction
  · have hc : 1 ^ 2 ≡ 4 [ZMOD 5] := by
      calc
        1 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at hc -- contradiction
  · left
    apply h
  · right
    apply h
  · dsimp [Int.ModEq] at h
    dsimp [(· ∣ ·)] at h
    obtain ⟨k, hk⟩ := h
    have hc : 4 ≡ 1 [ZMOD 5] := by
      calc
        4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
        _ = (n - 4) ^ 2 + 8 * (n - 4) + 16 := by ring
        _ = (5 * k) ^ 2 + 8 * (5 * k) + 16 := by rw [hk]
        _ = 5 * (5 * k ^ 2 + 8 * k + 3) + 1 := by ring
        _ ≡ 1 [ZMOD 5] := by extra
    numbers at hc -- contradiction

--# Exercise 4.4.6.3
@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intro m hml hmr
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

/- # Problem 2 -/

--# Example 4.5.4
@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, h⟩ := h
  obtain hn | hn := le_or_succ_le n 1
  · have hc : 2 ≤ 1 := by
      calc
        2 = n ^ 2 := by rw [h]
        _ ≤ 1 ^ 2 := by rel [hn]
        _ = 1 := by numbers
    numbers at hc
  · have hc : 4 ≤ 2 := by
      calc
        4 = 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]
        _ = 2 := by rw [h]
    numbers at hc

--# Example 4.5.5
@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h :=
      calc
        0 ≡ n [ZMOD 2] := by rel [h2]
        _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h -- contradiction
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

--# Example 4.5.6
@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
      calc
        (0 : ℤ) = 0 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
      calc 1 = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction
  · have h :=
      calc
        1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction
