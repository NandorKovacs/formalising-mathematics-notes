/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics2026.Solutions.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  revert ha
  rw [tendsTo_def, tendsTo_def]
  intro ha ε hε
  specialize ha ε hε
  cases' ha with B ha
  use B
  intro n hn
  specialize ha n hn
  rw [<-abs_sub_comm]
  simp
  rw [neg_add_eq_sub]
  exact ha

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  -- decompose TendsTo objects to convergence definitions
  rw [tendsTo_def] at *
  intro ε hε --introduce ε from the goal

  specialize ha (ε/2) (by linarith) -- restrict delta of the convergence of a(t) to ε / 2
  specialize hb (ε/2) (by linarith)

  cases' ha with Ba ha
  cases' hb with Bb hb
  use max Bb Ba -- take the bigger delta of the two convergences

  intro n hn -- introduce n and n ≤ max Bb Ba
  specialize ha n -- use the same n for both convergent series a(t) and b(u)
  specialize hb n

  rewrite [max_le_iff] at hn -- decompose max Ba Bb ≤ n to Bb ≤ n ∧ Ba ≤ n
  specialize ha hn.right -- fulfill Ba ≤ n and Bb ≤ n for the two convergence definitions
  specialize hb hn.left

  rw [abs_lt] at * -- finish calc
  constructor <;> linarith






/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
    apply tendsTo_add
    exact ha
    apply tendsTo_neg
    exact hb


end Section2sheet5
