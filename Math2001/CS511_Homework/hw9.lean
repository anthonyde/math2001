import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Data.Real.Basic

math2001_init

/-! # CS511 Homework 9 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · rw [c]
    use 3
    numbers
  · obtain ⟨m, hm⟩ := IH
    use 3 * m - 4
    rw [c, hm]
    ring

-- Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]
    numbers
  · rw [c, IH]
    ring

-- Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · rw [y]
    numbers
  · rw [y, IH]
    ring

/- # Exercise 4 -/

-- Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]
    numbers
  · rw [b]
    numbers
  · rw [b, IH1, IH2]
    ring

-- Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c']
    numbers
  · rw [c']
    numbers
  · rw [c', IH1]
    ring

-- Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]
    numbers
  · rw [t]
    numbers
  · rw [t, IH1, IH2]
    ring

/- # Problem 2 -/

-- Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ n : ℕ,
      (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5])
    ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n + 1) ≡ 2 [ZMOD 5])
  · intro n
    two_step_induction n with k IH1 IH2
    · left
      constructor
      · rw [s]
        numbers
      · rw [s]
        numbers
    · right
      constructor
      · rw [s]
        numbers
      · calc
          s (1 + 1) = s (0 + 2) := by ring
          _ = 2 * 3 + 3 * 2 := by rw [s, s, s]
          _ = 5 * 2 + 2 := by numbers
          _ ≡ 2 [ZMOD 5] := by extra
    · obtain ⟨IH2a, IH2b⟩ | ⟨IH2a, IH2b⟩ := IH2
      · right
        constructor
        · exact IH2b
        · calc
            s (k + 1 + 1 + 1) = 2 * s (k + 1 + 1) + 3 * s (k + 1) := by rw [s]
            _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [IH2a, IH2b]
            _ = 5 * 2 + 2 := by numbers
            _ ≡ 2 [ZMOD 5] := by extra
      · left
        constructor
        · exact IH2b
        · calc
            s (k + 1 + 1 + 1) = 2 * s (k + 1 + 1) + 3 * s (k + 1) := by rw [s]
            _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [IH2a, IH2b]
            _ = 5 * 2 + 3 := by numbers
            _ ≡ 3 [ZMOD 5] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
  · left
    exact H1
  · right
    exact H1

-- Exercise 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc
      r 7 = 140 := by rfl
      _ ≥ 2 ^ 7 := by numbers
  · calc
      r 8 = 338 := by rfl
      _ ≥ 2 ^ 8 := by numbers
  · calc
      r (k + 1 + 1) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ = 2 ^ (k + 1 + 1) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 1 + 1) := by extra
