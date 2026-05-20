/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro pq
  constructor
  apply pq.mpr
  apply pq.mp

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  all_goals intro pq; rw [pq]


example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro pq qr
  rwa [pq]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  all_goals {
    intro h
    exact ⟨h.right, h.left⟩
  }

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  rintro ⟨⟨p,q⟩,r⟩
  exact ⟨p,q,r⟩
  rintro ⟨p,q,r⟩
  exact ⟨⟨p,q⟩,r⟩


example : P ↔ P ∧ True := by
  constructor
  all_goals intro h
  trivial
  exact h.1

example : False ↔ P ∧ False := by
  constructor
  intro f
  trivial
  intro h
  exact h.2

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro pq rs
  rw [pq, rs]

example : ¬(P ↔ ¬P) := by
  by_cases h : P
  all_goals
    by_contra hc
    have hh := h
    rewrite [hc] at h
    contradiction
