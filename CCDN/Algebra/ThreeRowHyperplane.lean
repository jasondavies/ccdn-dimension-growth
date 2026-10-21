/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! A bounded integral equation obtained from three independent rows.
Cramer's rule uses row-replacement determinants, so the same elementary
3! T³ bound controls both the coefficients and their common denominator. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma three_by_three_det_abs_le (M : Matrix (Fin 3) (Fin 3) ℤ) (T : ℕ)
    (hM : ∀ i j, |M i j| ≤ (T : ℤ)) :
    |M.det| ≤ 6 * (T : ℤ) ^ 3 := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) hM
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, Nat.factorial_succ,
    Nat.factorial_zero, Nat.reduceAdd, Nat.reduceMul, nsmul_eq_mul, Nat.cast_ofNat] using hh

/-- The bounded row relation in integral coordinates. In particular the
coefficient multiplying the extra row is nonzero, without clearing a further
denominator after solving the linear system. -/
theorem exists_bounded_three_row_relation
    (M : Matrix (Fin 3) (Fin 3) ℤ) (w : Fin 3 → ℤ) (T : ℕ)
    (hM : ∀ i j, |M i j| ≤ (T : ℤ))
    (hw : ∀ j, |w j| ≤ (T : ℤ)) (hdet : M.det ≠ 0) :
    ∃ a : Fin 3 → ℤ,
      (∀ j, ∑ i, a i * M i j = M.det * w j) ∧
      (∀ i, |a i| ≤ 6 * (T : ℤ) ^ 3) ∧
      M.det ≠ 0 ∧ |M.det| ≤ 6 * (T : ℤ) ^ 3 := by
  let a := M.transpose.cramer w
  refine ⟨a, ?_, ?_, hdet, three_by_three_det_abs_le M T hM⟩
  · have hh := Matrix.mulVec_cramer M.transpose w
    rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hh
    intro j
    simpa only [a, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hh j
  · intro i
    change |M.transpose.cramer w i| ≤ _
    rw [Matrix.cramer_transpose_apply]
    apply three_by_three_det_abs_le (M.updateRow i w) T
    intro j k
    by_cases hji : j = i
    · subst j
      simpa using hw k
    · rw [Matrix.updateRow_ne hji]
      exact hM j k

end
end CCDN
