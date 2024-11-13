import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import Mathlib.Data.Real.Basic

math2001_init

open Function
namespace Int

/-! # CS511 Homework 10 Lean Exercises -/

/- # Exercise 3 -/

-- Exercise 8.1.13.2

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor <;> numbers

-- Exercise 8.1.13.3

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x y H
  calc
    x = (3 * x - 1 + 1) / 3 := by ring
    _ = (3 * y - 1 + 1) / 3 := by rw [H]
    _ = y := by ring

-- Exercise 8.1.13.5

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro x
  use x / 2
  ring

/- # Exercise 4 -/

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

-- Exercise 8.1.13.8

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor
  · rw [h, h]
  · exhaust

-- Exercise 8.1.13.9

example : Surjective h := by
  dsimp [Surjective]
  intro x
  cases x
  · use porthos
    exhaust
  · use athos
    exhaust

-- Exercise 8.1.13.11

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

/- # Problem 2 -/

-- Exercise 8.1.13.13

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  dsimp [Injective]
  intro f hf
  intro x y h
  apply hf
  calc
    f x = f x + 1 - 1 := by ring
    _ = f y + 1 - 1 := by rw [h]
    _ = f y := by ring

-- Exercise 8.1.13.14

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  dsimp [Injective]
  push_neg
  use fun x ↦ -1 * x
  constructor
  · intro x y h
    cancel -1 at h
  · use -1, 1
    constructor <;> numbers

-- Exercise 8.1.13.16

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]
  push_neg
  use 0, 1
  intro x
  conv => lhs; ring
  numbers
