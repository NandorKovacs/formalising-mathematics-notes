/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2026.Solutions.Section02reals.Sheet5
-- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rewrite [tendsTo_def] at *
  intro ε hε
  specialize h (ε/37) (by linarith)
  cases' h with B h
  use B
  intro n hn
  specialize h n hn
  rw [abs_lt] at *
  constructor <;> linarith

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rewrite [tendsTo_def] at *

  intro ε hε

  -- specialize h (ε / c) (div_pos hε hc)
  have hcc : (0 < ε / c) := by
    rewrite [<- mul_lt_mul_iff_left₀ hc]
    rewrite [zero_mul]
    rewrite [div_mul_cancel₀ ε (ne_of_gt hc)]
    exact hε
  specialize h (ε / c) hcc

  cases' h with B h
  use B

  intro n hn
  specialize h n hn

  rw [<-mul_sub, abs_mul]
  rw [abs_of_pos hc]
  -- exact?
  -- exact (lt_div_iff₀' hc).mp h
  rw [div_eq_inv_mul] at h
  rewrite [mul_comm] at h

  have hh := mul_lt_mul_of_pos_right h hc
  rewrite (occs := .pos [2]) [mul_comm] at hh
  rewrite (occs := .pos [3]) [mul_comm] at hh
  rewrite [mul_inv_cancel_left₀ (ne_of_gt hc)] at hh
  rw [mul_comm]
  exact hh


/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    have hnc : (0 < (-c)) := by linarith
    have hh := tendsTo_pos_const_mul h hnc

    rewrite [tendsTo_def] at hh ⊢

    intro ε hε
    specialize hh ε hε
    cases' hh with B hh
    use B
    intro n hn
    specialize hh n hn

    rw [<-mul_sub] at hh ⊢
    rw [<-abs_neg, <-neg_one_mul, <-mul_assoc] at hh
    rw (occs := .pos [2]) [mul_comm] at hh
    rw [mul_neg_one, neg_neg] at hh

    exact hh

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  by_cases hc:(c<0)
  exact tendsTo_neg_const_mul h hc
  by_cases hcc:(c>0)
  exact tendsTo_pos_const_mul h hcc
  have h0 : c=0:= by
    rw [not_lt] at hc hcc
    rw [eq_of_ge_of_le hc hcc]

  rewrite [tendsTo_def]
  intro ε hε
  use 0
  intro n hn

  rw [h0, zero_mul, zero_mul, sub_zero]
  norm_num
  exact hε

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
sorry

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  sorry

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  sorry

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  sorry

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
