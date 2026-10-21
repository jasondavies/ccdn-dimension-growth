/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.LinearCombination

/-! A counterexample to the numerical constant printed in CCDN Lemma 5.4.
The system has five independent equations in six variables, all coefficients
bounded by ten. Every integer solution of the last four equations that
violates the first has a coordinate of absolute value at least 120050,
whereas the printed bound is 120000. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped BigOperators

/-- The first equation is x4=0; the unused sixth coordinate preserves s<r. -/
def separatorCounterexampleMatrix : Matrix (Fin 5) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     10, 10, 10, 10, -3, 0;
     10, -9, 8, -8, -6, 0;
     9, 8, -10, -10, -5, 0;
     9, -9, -9, 10, 9, 0]

lemma separatorCounterexample_coeff_le (i : Fin 5) (j : Fin 6) :
    |separatorCounterexampleMatrix i j| ≤ (10 : ℤ) := by
  fin_cases i <;> fin_cases j <;> norm_num [separatorCounterexampleMatrix]

lemma separatorCounterexample_independent :
    LinearIndependent ℚ (fun i => fun j => (separatorCounterexampleMatrix i j : ℚ)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  have h3 := congrFun hc 3
  have h4 := congrFun hc 4
  norm_num [Fin.sum_univ_succ, separatorCounterexampleMatrix] at h0 h1 h2 h3 h4
  fin_cases i
  · change c 0 = 0; linarith
  · change c 1 = 0; linarith
  · change c 2 = 0; linarith
  · change c 3 = 0; linarith
  · change c 4 = 0; linarith

lemma separatorCounterexample_first (x : Fin 6 → ℤ) :
    (∑ j, separatorCounterexampleMatrix 0 j * x j) = x 4 := by
  simp [Fin.sum_univ_succ, separatorCounterexampleMatrix]

/-- An exact integral row-combination certificate. -/
lemma separatorCounterexample_divisibility (x : Fin 6 → ℤ)
    (hx : ∀ i : Fin 5, i ≠ 0 → ∑ j, separatorCounterexampleMatrix i j * x j = 0) :
    (120050 : ℤ) ∣ x 4 := by
  have h1 := hx 1 (by decide)
  have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide)
  have h4 := hx 4 (by decide)
  norm_num [Fin.sum_univ_succ, separatorCounterexampleMatrix] at h1 h2 h3 h4
  refine ⟨-2444 * x 2 - 1769 * x 3, ?_⟩
  linear_combination 11594083 * h1 + 2651360 * h2 - 13796060 * h3 - 2032210 * h4

lemma separatorCounterexample_coordinate_large (x : Fin 6 → ℤ)
    (hfirst : (∑ j, separatorCounterexampleMatrix 0 j * x j) ≠ 0)
    (hother : ∀ i : Fin 5, i ≠ 0 → ∑ j, separatorCounterexampleMatrix i j * x j = 0) :
    (120050 : ℤ) ≤ |x 4| := by
  rw [separatorCounterexample_first] at hfirst
  exact Int.le_abs_of_dvd hfirst (separatorCounterexample_divisibility x hother)

lemma separatorCounterexample_printed_bound :
    Real.sqrt (((5 - 1 : ℕ).factorial : ℝ) * 6) * (10 : ℝ) ^ (5 - 1 : ℕ) = 120000 := by
  have hs : Real.sqrt 144 = 12 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num [Nat.factorial, hs]

/-- The concrete matrix satisfies every linear-algebra hypothesis of printed
Lemma 5.4 but has no integer separator within its displayed bound. -/
theorem no_separator_at_printed_bound :
    LinearIndependent ℚ (fun i => fun j => (separatorCounterexampleMatrix i j : ℚ)) ∧
      (∀ i j, |separatorCounterexampleMatrix i j| ≤ (10 : ℤ)) ∧
      ¬ ∃ x : Fin 6 → ℤ,
        (∑ j, separatorCounterexampleMatrix 0 j * x j) ≠ 0 ∧
        (∀ i : Fin 5, i ≠ 0 → ∑ j, separatorCounterexampleMatrix i j * x j = 0) ∧
        ∀ j, (|x j| : ℝ) ≤
          Real.sqrt (((5 - 1 : ℕ).factorial : ℝ) * 6) * (10 : ℝ) ^ (5 - 1 : ℕ) := by
  refine ⟨separatorCounterexample_independent, separatorCounterexample_coeff_le, ?_⟩
  rintro ⟨x, hfirst, hother, hbound⟩
  have hlo : (120050 : ℝ) ≤ (|x 4| : ℝ) := by
    exact_mod_cast separatorCounterexample_coordinate_large x hfirst hother
  have hhi := hbound 4
  rw [separatorCounterexample_printed_bound] at hhi
  linarith

/-- Negation of the universal numerical bound printed in Lemma 5.4,
with s+1 independent equations in r variables. -/
theorem not_printed_row_separator_bound :
    ¬ (∀ (s r B : ℕ), 0 < B → s + 1 < r →
      ∀ (A : Matrix (Fin (s + 1)) (Fin r) ℤ),
        LinearIndependent ℚ (fun i => fun j => (A i j : ℚ)) →
        (∀ i j, |A i j| ≤ (B : ℤ)) →
        ∃ x : Fin r → ℤ, x ≠ 0 ∧
          (∑ j, A 0 j * x j) ≠ 0 ∧
          (∀ i : Fin (s + 1), i ≠ 0 → ∑ j, A i j * x j = 0) ∧
          ∀ j, (|x j| : ℝ) ≤ Real.sqrt ((s.factorial : ℝ) * r) * (B : ℝ) ^ s) := by
  intro h
  obtain ⟨x, _, hfirst, hother, hbound⟩ := h 4 6 10 (by decide) (by decide)
    separatorCounterexampleMatrix separatorCounterexample_independent
    separatorCounterexample_coeff_le
  exact no_separator_at_printed_bound.2.2 ⟨x, hfirst, hother, hbound⟩

end
end CCDN
