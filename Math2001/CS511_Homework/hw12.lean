import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-! # CS511 Homework 12 Lean Exercises -/

/- # Exercise 4 -/

-- Exercise 6.4.3.1
theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain ⟨k, hk⟩ | h := even_or_odd n
  · have IH := extract_pow_two k
    rw [hk] at hn
    cancel 2 at hn
    obtain ⟨a, x, ⟨h1, h2⟩⟩ := IH hn
    use (a + 1), x
    constructor
    · assumption
    · rw [hk, h2]
      ring
  · use 0, n
    constructor
    · assumption
    · ring

/- # Exercise 5 -/

-- Exercise 9.1.10.1
example : 4 ∉ {a : ℚ | a < 3} := by
  intro h
  contradiction

-- Exercise 9.1.10.2
example : 6 ∈ {n : ℕ | n ∣ 42} := by
  use 7
  numbers

-- Exercise 9.1.10.3
example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  trivial

/- # Exercise 6 -/

-- Exercise 9.1.10.6
example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  intro x ⟨n, hn⟩
  use 4 * n
  rw [hn]
  ring

-- Exercise 9.1.10.7
example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  · use 1
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers

-- Exercise 9.2.8.5
example : {r : ℤ | r ≡ 7 [ZMOD 10]}
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  intro x ⟨n, h⟩
  dsimp
  constructor
  · use 5 * n + 3
    calc
      x - 1 = x - 7 + 6 := by ring
      _ = 10 * n + 6 := by rw [h]
      _ = 2 * (5 * n + 3) := by ring
  · use 2 * n + 1
    calc
      x - 2 = x - 7 + 5 := by ring
      _ = 10 * n + 5 := by rw [h]
      _ = 5 * (2 * n + 1) := by ring

/- # Problem 2 -/

-- Exercise 9.2.8.6
example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

-- Exercise 9.3.6.1
def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬Injective r := by
  dsimp [Injective, r]
  push_neg
  use {3}, ∅
  dsimp
  constructor
  · ext x
    dsimp
    exhaust
  · apply singleton_ne_empty
