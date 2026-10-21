/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.CenterProjectionHeight
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Center.GeometricProjectiveCurveProjection
import CCDN.Center.ProjectiveClosureRecovery
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Hilbert.HilbertPolynomialComparison
import CCDN.Hilbert.ZeroDimensionalGeometricPoint
/-! Numerical bounds for the row-resultant good-center detector. Its degree
D(2d-1) is strictly smaller than D^2 in positive projective dimension, and
a geometrically integral source of dimension zero has degree one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma hilbert_multiplicity_pos_of_prime {K : Type*} [Field K] {n m d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) [J.IsPrime]
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / m.factorial) : 1 ≤ d := by
  have hp := filteredHilbertPolynomial_leadingCoeff_pos J (Ideal.IsPrime.ne_top ‹J.IsPrime›)
  rw [hdegree] at hp
  by_contra hd
  have hz : d = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_div] at hp
  exact lt_irrefl 0 hp

/-- A geometrically integral zero-dimensional projective source has degree one. -/
theorem geometric_projective_dimension_zero_multiplicity_one
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ)) : d = 1 := by
  classical
  obtain ⟨j,hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J (by omega)
  let e := Equiv.swap 0 j
  let J' := projectivePermutedIdeal J e
  have : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  let : (J'.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime J e
  have hJ' := projectivePermutedIdeal_homogeneous J hJ e
  have hX : X 0 ∉ J' := by
    change X 0 ∉ projectivePermutedIdeal J e
    rw [mem_projectivePermutedIdeal,rename_X]
    simpa only [e,Equiv.swap_apply_left] using hj
  have hp := projectivePermutedIdeal_filteredHilbertPolynomial J e
  have hdim' : (filteredHilbertPolynomial J').natDegree = 0 + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  have hd' : (filteredHilbertPolynomial J').leadingCoeff = (d : ℚ) / (0 + 1).factorial := by
    simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, div_one] using
      (congrArg Polynomial.leadingCoeff hp).trans hdegree
  obtain ⟨hmI,hdI⟩ :=
    projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX 0 d ⟨hdim', hd'⟩
  let : ((projectiveChartIdeal J').map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    projectiveChartIdeal_geometrically_prime J' hX
  obtain ⟨_,_,hpoly⟩ := zero_dimensional_geometrically_integral_point
    (L := AlgebraicClosure K) (projectiveChartIdeal J') hmI
  have hq : (1 : ℚ) = d := by
    simpa only [hpoly,Polynomial.leadingCoeff_one,Nat.factorial_zero,Nat.cast_one,div_one] using hdI
  exact_mod_cast hq.symm

lemma center_detector_degree_lt_square {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) :
    ((m + 1) * d) * (2 * d - 1) < ((m + 1) * d) ^ 2 := by
  have hD : 0 < (m + 1) * d := by positivity
  have hbig : 2 * d ≤ (m + 1) * d := by nlinarith
  have hsmall : 2 * d - 1 < (m + 1) * d := by omega
  nlinarith

lemma center_detector_degree_le_square {m d : ℕ}
    (hd : 1 ≤ d) (hboundary : 1 ≤ m ∨ d = 1) :
    max 1 (((m + 1) * d) * (2 * d - 1)) ≤ (m + 1) ^ 2 * d ^ 2 := by
  have hD : 1 ≤ (m + 1) * d := by nlinarith
  rw [← mul_pow]
  apply max_le (one_le_pow₀ hD)
  rcases hboundary with hm | rfl
  · exact (center_detector_degree_lt_square hm hd).le
  · simp only [mul_one, Nat.reduceSub]
    nlinarith

/-- The printed projection-height exponent also covers the empty center. -/
lemma center_projection_source_exponent_all_rows {m n r d : ℕ}
    (hrn : r ≤ n + 1) (hmn : m + 1 ≤ n + 1) (hd : 1 ≤ d) :
    (n + 1) * (2 * r.factorial * ((m + 1) ^ 2 * d ^ 2) ^ r) ≤
      centerProjectionHeightConstant n * d ^ (2 * r ^ 2) := by
  by_cases hr : r = 0
  · subst r
    norm_num only [Nat.factorial_zero, mul_one, pow_zero]
    unfold centerProjectionHeightConstant
    have hf : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
    have hp : 1 ≤ (n + 1) ^ (2 * (n + 1)) := one_le_pow₀ (by omega)
    calc
      (n + 1) * 2 = 2 * (n + 1) * 1 * 1 := by ring
      _ ≤ 2 * (n + 1) * (n + 1).factorial * (n + 1) ^ (2 * (n + 1)) := by gcongr
  · exact center_projection_source_exponent (by omega) hrn hmn hd

lemma geometric_projective_multiplicity_boundary
    {K : Type*} [Field K] [CharZero K] {n m d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdimdeg : HasProjectiveDimensionDegree J m d) :
    1 ≤ m ∨ d = 1 := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  by_cases hm : m = 0
  · right
    subst m
    exact geometric_projective_dimension_zero_multiplicity_one J hJ d hdim
      (by simpa only [Nat.zero_add,Nat.factorial_one,Nat.cast_one,div_one] using hdegree)
  · exact Or.inl (by omega)

end
end CCDN
