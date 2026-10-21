/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormParameterDegree
public import CCDN.ForMathlib.MatrixRank
public import CCDN.Algebra.IntegerPolynomialAvoidance
public import CCDN.Projection.LinearProjectionFiltration
public import CCDN.Projection.PrimitiveNormalization
/-! The numerical specialization step for a nonempty polynomial condition on
maximal minors. The geometric construction of a good-center condition is
separate: this module starts with a polynomial and a full-rank rational
matrix where it does not vanish. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Denominator clearing transfers the integer grid lemma to rational
polynomials without increasing the grid size. -/
theorem exists_integer_grid_rational_eval_ne_zero {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℚ) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧
      eval (fun i => (v i : ℚ)) f ≠ 0 := by
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model f hf
  have hg : g ≠ 0 := by
    intro hz
    have hh : C a * f = 0 := by simpa only [hz, map_zero] using he.symm
    exact mul_ne_zero (C_eq_zero.not.mpr ha) hf hh
  obtain ⟨v, hv, hvg⟩ := exists_integer_grid_eval_ne_zero g hg A
    ((rational_scalar_model_degree ha hf he).trans_le hd)
  refine ⟨v, hv, ?_⟩
  intro hz
  have hgzero := (rational_scalar_model_zero_iff ha he (fun i => (v i : ℚ))).mpr hz
  have hh : ((eval v g : ℤ) : ℚ) = 0 := by
    exact (map_eval (Int.castRingHom ℚ) v g).trans hgzero
  exact hvg (Int.cast_eq_zero.mp hh)

end
end CCDN
