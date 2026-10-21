/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
import CCDN.Algebra.ScaledHomogenization
/-! The restriction of a bounded homogenization to the hyperplane at infinity
is exactly its highest indicated homogeneous component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem scaledHomogenize_one_eval_at_infinity {K : Type*} [Field K] {n D : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ D) (b : Fin n → K) :
    eval (Fin.cons 0 b) (scaledHomogenize D 1 f) =
      eval b (homogeneousComponent D f) := by
  classical
  rw [scaledHomogenize, map_sum, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_monomial, homogenizedExponent_value]
  have hle : e.sum (fun _ k => k) ≤ D := (le_totalDegree he).trans hf
  by_cases h : e.degree = D
  · have heq : e.sum (fun _ k => k) = D := h
    simp [h, heq, eval_monomial]
  · have hpos : 0 < D - e.sum (fun _ k => k) := by
      change e.sum (fun _ k => k) ≠ D at h
      omega
    simp [h, zero_pow (Nat.ne_of_gt hpos)]

end
end CCDN
