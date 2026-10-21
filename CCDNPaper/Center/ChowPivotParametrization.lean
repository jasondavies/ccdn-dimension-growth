/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring

/-! A denominator-free parametrization of hyperplane tuples through a
cone point, using an arbitrary nonzero pivot coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The hyperplane tuple obtained from coefficients `v` and a point `x` by using coordinate `j`
as pivot: off the pivot column the coefficient is `v q * x j`, and in the pivot column it is
`-∑ k ≠ j, v (i, k) * x k`, so that every resulting hyperplane passes through `x`. -/
def chowPivotCoefficients {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K)
    (v : Fin r × Fin (n + 1) → K) : Fin r × Fin (n + 1) → K :=
  fun q => if q.2 = j then -(∑ k ∈ Finset.univ.erase j, v (q.1,k) * x k)
    else v q * x j

/-- The polynomial version of `chowPivotCoefficients j x v`, with the point `x` replaced by the
coordinate variables: a family of linear forms in `X 0, …, X n` whose evaluation at `x` gives the
pivot parametrization of hyperplanes through `x`. -/
def chowPivotPolynomials {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K) :
    Fin r × Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  fun q => if q.2 = j then -(∑ k ∈ Finset.univ.erase j, C (v (q.1,k)) * X k)
    else C (v q) * X j

/-- Evaluating `chowPivotPolynomials j v` at a point `x` gives `chowPivotCoefficients j x v`. -/
lemma chowPivotPolynomials_eval {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (v : Fin r × Fin (n + 1) → K)
    (x : Fin (n + 1) → K) (q : Fin r × Fin (n + 1)) :
    eval x (chowPivotPolynomials j v q) = chowPivotCoefficients j x v q := by
  simp only [chowPivotPolynomials, chowPivotCoefficients]
  split_ifs <;> simp

/-- Every hyperplane in the pivot parametrization `chowPivotCoefficients j x v` passes through
the point `x`. -/
lemma chowPivotCoefficients_relation {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K)
    (v : Fin r × Fin (n + 1) → K) (i : Fin r) :
    ∑ k, chowPivotCoefficients j x v (i,k) * x k = 0 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ k ∈ Finset.univ.erase j, chowPivotCoefficients j x v (i,k) * x k) =
      (∑ k ∈ Finset.univ.erase j, v (i,k) * x k) * x j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [chowPivotCoefficients, ite_eq_right (Finset.mem_erase.mp hk).1]
    ring
  rw [he, chowPivotCoefficients, ite_eq_left rfl]
  ring

/-- If the pivot coordinate `x j` is nonzero, every hyperplane tuple `U` through `x` arises from
the pivot parametrization, namely as `chowPivotCoefficients j x (U / x j)`. -/
lemma chowPivotCoefficients_reconstruct {K : Type*} [Field K] {n r : ℕ}
    (j : Fin (n + 1)) (x : Fin (n + 1) → K) (hx : x j ≠ 0)
    (U : Fin r × Fin (n + 1) → K)
    (hU : ∀ i, ∑ k, U (i,k) * x k = 0) :
    chowPivotCoefficients j x (fun q => U q / x j) = U := by
  classical
  funext q
  rcases q with ⟨i,k⟩
  by_cases hk : k = j
  · subst k
    rw [chowPivotCoefficients, ite_eq_left rfl]
    apply mul_right_cancel₀ hx
    have he : (∑ k ∈ Finset.univ.erase j, U (i,k) / x j * x k) * x j =
        ∑ k ∈ Finset.univ.erase j, U (i,k) * x k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    rw [neg_mul, he]
    have hh := hU i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hh
    exact (eq_neg_of_add_eq_zero_right hh).symm
  · rw [chowPivotCoefficients, ite_eq_right hk, div_mul_cancel₀ _ hx]

end
end CCDN
