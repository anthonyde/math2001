import AutograderLib
import Library.Basic

math2001_init

/-! # CS511 Homework 7 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 5.1.7.6
@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨hPQ, hQP⟩ := h
  constructor <;> intro h'
  · obtain ⟨hP, hR⟩ := h'
    constructor
    · apply hPQ
      apply hP
    · apply hR
  · obtain ⟨hQ, hR⟩ := h'
    constructor
    · apply hQP
      apply hQ
    · apply hR

-- Exercise 5.1.7.8
@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor <;>
  · intro h
    obtain h | h := h
    · right
      apply h
    · left
      apply h

-- Exercise 5.1.7.9
@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor <;> intro h
  · constructor
    · intro hP
      apply h
      left
      apply hP
    · intro hQ
      apply h
      right
      apply hQ
  · obtain ⟨hcP, hcQ⟩ := h
    intro hPQ
    obtain hP | hQ := hPQ <;> contradiction

/- # Exercise 4 -/

-- Exercise 5.1.7.11
@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro hP
    obtain ⟨x, hP⟩ := hP
    use x
    apply Iff.mp (h x)
    apply hP
  · intro hQ
    obtain ⟨x, hQ⟩ := hQ
    use x
    apply Iff.mpr (h x)
    apply hQ

-- Exercise 5.1.7.12
@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor <;>
  · intro h
    obtain ⟨x, y, hP⟩ := h
    use y, x
    apply hP

-- Exercise 5.1.7.13
@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor <;>
  · intro hxyP y x
    apply hxyP x y

/- # Problem 2 -/

-- Exercise 5.1.7.14
@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor <;> intro h
  · obtain ⟨⟨x, hP⟩, hQ⟩ := h
    use x
    constructor
    · apply hP
    · apply hQ
  · obtain ⟨x, hP, hQ⟩ := h
    constructor
    · use x
      apply hP
    · apply hQ

-- Exercise 5.2.7.2
@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h hQ
    by_cases hP : P
    · apply hP
    · have hc := h hP
      contradiction
  · intro h hP
    by_cases hQ : Q
    · have hc := h hQ
      contradiction
    · apply hQ
