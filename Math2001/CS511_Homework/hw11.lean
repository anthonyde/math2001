import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.InjectiveSurjective
import Mathlib.Data.Real.Basic

math2001_init

open Function

/-! # CS511 Homework 11 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 8.3.10.2
def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  constructor <;>
  · ext x
    dsimp [comp, id, u, v]
    ring

-- Exercise 8.3.10.3
example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  intro x y h
  apply hf
  apply hg
  exact h

-- Exercise 8.3.10.4
example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [hx, hy]

/- # Exercise 4 -/

-- Exercise 8.4.10.1
example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  constructor
  · intro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    dsimp at h
    obtain ⟨h1, h2⟩ := h
    constructor
    · rw [h1] at h2
      calc
        x1 = x1 - y2 + y2 := by ring
        _ = y1 - y2 + y2 := by rw [h2]
        _ = y1 := by ring
    · exact h1
  · intro ⟨x1, x2⟩
    use (x1 + x2, x1)
    ring

-- Exercise 8.4.10.2.1
example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (0, 1), (2, 2)
  dsimp
  constructor
  · ring
  · numbers

-- Exercise 8.4.10.2.2
example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  intro x
  use ⟨3 * x + 1, x⟩
  ring

/- # Problem 2 -/

-- Exercise 8.3.10.5
example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  choose g hg using hf
  use g
  ext x
  dsimp
  exact hg x

-- Exercise 8.3.10.7
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  obtain ⟨g1f, fg1⟩ := h1
  obtain ⟨g2f, fg2⟩ := h2
  ext x
  calc
    g1 x = id (g1 x) := by rfl
    _ = (g2 ∘ f) (g1 x) := by rw [g2f]
    _ = g2 ((f ∘ g1) x) := by rfl
    _ = g2 (id x) := by rw [fg1]
    _ = g2 x := by rfl
