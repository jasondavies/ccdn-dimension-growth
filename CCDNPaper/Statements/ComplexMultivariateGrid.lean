/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousTranslation
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousChart
import CCDN.Height.MultivariateGridHeight
import CCDN.Plane.HomogeneousLeadingCoefficient

/-! Sharp complex integer-grid bounds for homogeneous polynomials. The affine
grid bound of `CCDN.Height.MultivariateGridHeight` proves the exact coefficient-positioning
constant in CCDN Lemma 3.4.2. The distinguished homogeneous coordinate is indexed first. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN Lemma 3.4.2, with the fixed homogeneous coordinate placed first.
The bound is simultaneous for all coefficients and has the exact factor 3^(nd). -/
theorem exists_complex_homogeneous_grid_height_witness {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℂ) (hf : f.IsHomogeneous d) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧ ∀ m,
      ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) *
        ‖eval (Fin.cons 1 (fun i => (a i : ℂ))) f‖ := by
  obtain ⟨a, ha, hcoeff⟩ := exists_complex_multivariate_grid_height_witness (affineChart n f)
    ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  refine ⟨a, ha, ?_⟩
  intro m
  by_cases hm : m.sum (fun _ e => e) = d
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
    rw [← affineChart_homogeneous_coefficient f hf j, ← affineChart_eval]
    exact hcoeff _
  · rw [hf.coeff_eq_zero hm, norm_zero]
    positivity


/-- A bounded integer shear places the sharp complex grid witness in the
leading coefficient, without changing homogeneous degree. -/
theorem exists_complex_bounded_leading_coefficient_translation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℂ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f) ≠ 0 ∧
      ∀ m, ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) *
        ‖MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f)‖ := by
  obtain ⟨a, ha, hcoeff⟩ := exists_complex_homogeneous_grid_height_witness f hf
  have hval : eval (Fin.cons 1 (fun i => (a i : ℂ))) f ≠ 0 := by
    intro hz
    apply hf0
    apply MvPolynomial.ext
    intro m
    have hh := hcoeff m
    rw [hz, norm_zero, mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  have he := homogeneousTranslation_pure_first (fun i => (a i : ℂ)) f hf
  have hlc := lex_leadingCoeff_eq_pure_first
    (homogeneousTranslation ℂ (fun i => (a i : ℂ)) f)
    (homogeneousTranslation_homogeneous _ hf).totalDegree_le (he ▸ hval)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hlc, he]
    exact hval
  · intro m
    rw [hlc, he]
    exact hcoeff m

end
end CCDN
