/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerFactorKernel
/-! A nonzero Euler kernel vector forces every maximal universal
coefficient minor to vanish after specialization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

theorem eulerClosedForm_minor_eq_zero_of_kernel
    {F : Type*} [Field F] (k : ℕ) (f : Polynomial (Polynomial F))
    (u : EulerPairSpace F k) (hu : u ≠ 0)
    (hker : eulerClosedFormOperator k f u = 0)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k f).submatrix rows cols).det = 0 := by
  classical
  by_contra hdet
  let A := eulerClosedFormCoefficientMatrix k f
  have hlo : (k + 2) ^ 2 - 1 ≤ A.rank := by
    have hh := Matrix.rank_submatrix_le A rows cols
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hh
    exact hh
  have hr : A.rank = Fintype.card (EulerColumns k) := by
    apply le_antisymm (Matrix.rank_le_card_width _)
    simpa only [card_eulerColumns] using hlo
  have hi : LinearIndependent F A.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Matrix.rank_eq_finrank_span_cols, hr]
  let T := (bivariateCoefficients F).comp (eulerClosedFormOperator k f)
  have hsum : ∑ i, (eulerPairBasis F k).repr u i • A.col i = 0 := by
    have hh := congrArg T ((eulerPairBasis F k).sum_repr u)
    rw [map_sum] at hh
    simp only [map_smul] at hh
    change (∑ i, (eulerPairBasis F k).repr u i • A.col i) =
      bivariateCoefficients F (eulerClosedFormOperator k f u) at hh
    rw [hker, map_zero] at hh
    exact hh
  have hz := Fintype.linearIndependent_iff.mp hi _ hsum
  apply hu
  apply (eulerPairBasis F k).repr.injective
  ext i
  simpa only [map_zero, Finsupp.zero_apply] using hz i

end
end CCDN
