/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.ForMathlib.Polynomial
import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
import Mathlib.Algebra.Order.Star.Rat
/-! A nonempty standard chart recovers its homogeneous prime ideal
by projective closure. Its affine Hilbert dimension and multiplicity follow
from the cone Hilbert polynomial, in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma homogeneous_mem_projectiveChartIdeal_iff
    {K : Type*} [Field K] {n M : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hX : X 0 ∉ I) (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous M) :
    affineChart n f ∈ projectiveChartIdeal I ↔ f ∈ I := by
  let A := MvPolynomial (Fin (n + 1)) K ⧸ I
  let F := FractionRing A
  let q := IsScalarTower.toAlgHom K A F
  apply affineChart_mem_coordinate_kernel_iff I q (IsFractionRing.injective A F) _ f hf
  intro h
  apply hX
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (IsFractionRing.injective A F)
    (by change q ((Ideal.Quotient.mk I) (X 0)) = q 0; simpa only [map_zero] using h)

theorem projectiveClosureIdeal_chartIdeal_eq
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (hX : X 0 ∉ I) :
    projectiveClosureIdeal (projectiveChartIdeal I) = I := by
  classical
  ext f
  rw [mem_projectiveClosureIdeal_iff]
  simp only [homogeneous_mem_projectiveChartIdeal_iff I hX _
    (homogeneousComponent_isHomogeneous _ _)]
  constructor
  · intro h
    rw [← sum_homogeneousComponent f]
    exact I.sum_mem (fun N _ => h N)
  · exact hI f

theorem projectiveChartIdeal_hilbertPolynomial_parameters
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (hX : X 0 ∉ I) (m d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    (filteredHilbertPolynomial (projectiveChartIdeal I)).natDegree = m ∧
      (filteredHilbertPolynomial (projectiveChartIdeal I)).leadingCoeff =
        (d : ℚ) / m.factorial := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let Q := filteredHilbertPolynomial (projectiveChartIdeal I)
  have he := projectiveClosureIdeal_hilbertPolynomial_difference (projectiveChartIdeal I)
  rw [projectiveClosureIdeal_chartIdeal_eq I hI hX] at he
  have hf := And.intro
    (Polynomial.natDegree_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim 1 one_ne_zero)
    (Polynomial.leadingCoeff_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim 1
      one_ne_zero)
  rw [he] at hf
  have hQlc : (Q.comp (Polynomial.X + Polynomial.C 1)).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_X_add_C,
      one_pow, mul_one]
  refine ⟨?_, ?_⟩
  · simpa only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one] using hf.1
  · change Q.leadingCoeff = _
    have hh : Q.leadingCoeff = (d : ℚ) / (m + 1).factorial * (m + 1) := by
      calc
        Q.leadingCoeff = (Q.comp (Polynomial.X + Polynomial.C 1)).leadingCoeff := hQlc.symm
        _ = _ := by simpa only [hdegree, mul_one] using hf.2
    rw [hh, Nat.factorial_succ, Nat.cast_mul]
    have hm : (m + 1 : ℚ) ≠ 0 := by positivity
    have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

end
end CCDN
