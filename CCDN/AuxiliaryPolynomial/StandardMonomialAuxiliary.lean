/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import CCDN.ForMathlib.StandardExponents
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ArithmeticHeights.BombieriVaaler
import CCDN.Algebra.RowSelection

/-! Vanishing maximal determinants on a standard-monomial family produce
an integer auxiliary outside the original principal ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_standard_auxiliary_of_zero_determinants {n N t M : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (mon : Fin N → (Fin n →₀ ℕ))
    (hmon : Function.Injective mon)
    (hstd : ∀ j, mon j ∈ Ideal.standardExponents (Ideal.span {f}) MonomialOrder.degLex)
    (hdegree : ∀ j, (mon j).degree ≤ M)
    (x : Fin t → IntPoint n)
    (hdet : ∀ a : Fin N → Fin t, (evaluationMatrix mon (x ∘ a)).det = 0) :
    ∃ g : MvPolynomial (Fin n) ℤ, g ≠ 0 ∧
      ¬ f ∣ map (Int.castRingHom ℚ) g ∧ g.totalDegree ≤ M ∧
      ∀ i, eval (x i) g = 0 := by
  classical
  let A := evaluationMatrix mon x
  obtain ⟨r, a, _, hli, hspan, hr⟩ := exists_independent_spanning_rows (A.map ((↑) : ℤ → ℚ))
  have hrN : r < N := by
    by_contra hn
    have he : r = N := by omega
    subst r
    have hunit := Matrix.linearIndependent_row_iff_isUnit.mp hli
    have hnonzero := (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
    apply hnonzero
    have hd := congrArg (Int.castRingHom ℚ) (hdet a)
    have heA : (A.map ((↑) : ℤ → ℚ)).submatrix a id =
        (Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon (x ∘ a)) := by
      ext i j
      rfl
    rw [heA]
    simpa only [RingHom.map_det, map_zero] using hd
  let A' := evaluationMatrix mon (x ∘ a)
  have hli' : LinearIndependent ℚ (A'.map ((↑) : ℤ → ℚ)).row := hli
  obtain ⟨v, hv, hAv, _⟩ := Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow
    A' hli' (by simpa only [Fintype.card_fin] using hrN)
  let g := polynomialOfCoefficients mon v
  have hg0 : g ≠ 0 := polynomialOfCoefficients_ne_zero mon hmon hv
  have hgQ : map (Int.castRingHom ℚ) g ≠ 0 := by
    intro h
    exact hg0 ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using h))
  have hgstd : map (Int.castRingHom ℚ) g ∈
      restrictSupport ℚ (Ideal.standardExponents (Ideal.span {f}) MonomialOrder.degLex) := by
    intro m hm
    by_contra hbad
    have hne (j : Fin N) : mon j ≠ m := by
      intro he
      exact hbad (he ▸ hstd j)
    have hc : (map (Int.castRingHom ℚ) g).coeff m = 0 := by
      simp only [g, polynomialOfCoefficients, map_sum, map_monomial, coeff_sum,
        coeff_monomial, hne, ite_false, Finset.sum_const_zero]
    exact (mem_support_iff.mp hm) hc
  refine ⟨g, hg0, ?_, totalDegree_polynomialOfCoefficients_le mon v hdegree, ?_⟩
  · intro hdvd
    exact hgQ (Ideal.eq_zero_of_mem_restrictSupport_standardExponents (Ideal.span {f})
      MonomialOrder.degLex hgstd (Ideal.mem_span_singleton.mpr hdvd))
  · intro i
    apply vanishes_of_evaluation_row_mem_span mon (x ∘ a) v hAv
    change (A.map ((↑) : ℤ → ℚ)).row i ∈ _
    rw [show Submodule.span ℚ (Set.range ((evaluationMatrix mon (x ∘ a)).map
      ((↑) : ℤ → ℚ)).row) = Submodule.span ℚ (Set.range (A.map ((↑) : ℤ → ℚ)).row) from hspan]
    exact Submodule.subset_span ⟨i, rfl⟩

end
end CCDN
