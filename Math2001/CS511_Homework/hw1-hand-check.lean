import Library.Basic

math2001_init

/-! # CS511 Homework 1 Hand Exercises -/

-- Exercise 1
-- (i)
example {p q : Prop} (hp : p) : (p -> q) -> q :=
  fun hpq : p -> q => -- intro/assumption
    hpq hp                  -- elim to

-- (j)
example {p q r : Prop} (hprqr : (p -> r) /\ (q -> r)) : p /\ q -> r := by
  have hpr : p -> r := And.left hprqr -- elim and
  exact fun hpq : p /\ q =>           -- intro/assumption
    have hp := And.left hpq           -- elim and
    hpr hp                            -- elim to

-- (k)
example {p q r : Prop} (hqr : q -> r) : (p -> q) -> (p -> r) :=
  fun hpq : p -> q => -- intro/assumption
    fun hp : p =>           -- intro/assumption
      hqr (hpq hp)          -- elim to/elim to
