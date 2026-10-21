/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Curve.Curve
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.FieldTheory.Galois.Basic
import CCDN.Hypersurface.NonRationalVarietyCount
/-! Exact agreement of the affine curve degree interface with the
filtered Hilbert polynomial, and the nongeometric curve count. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma affineCurve_filteredHilbertPolynomial {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) (d : ℕ) (hd : HasAffineCurveDegree I d) :
    ∃ c : ℤ, filteredHilbertPolynomial I = Polynomial.C (d : ℚ) * Polynomial.X +
      Polynomial.C (c : ℚ) := by
  obtain ⟨N, c, hc⟩ := hd
  refine ⟨c, filteredHilbertPolynomial_eq_of_eventual I _ ⟨N, ?_⟩⟩
  intro M hM
  have he : (Module.finrank ℚ (filteredCoordinateSpace I M) : ℚ) =
      (d : ℚ) * (M : ℚ) + (c : ℚ) := by
    exact_mod_cast hc M hM
  simpa using he.symm

lemma affineCurve_filteredHilbertPolynomial_degree {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) (d : ℕ) (hd : 0 < d)
    (hdegree : HasAffineCurveDegree I d) :
    (filteredHilbertPolynomial I).natDegree = 1 ∧
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) := by
  obtain ⟨c, hc⟩ := affineCurve_filteredHilbertPolynomial I d hdegree
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  rw [hc]
  exact ⟨Polynomial.natDegree_linear hd0, Polynomial.leadingCoeff_linear hd0⟩

theorem nonabsolute_affine_curve_count_le_degree_sq
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d)
    (hred : ¬ (I.map (MvPolynomial.map (algebraMap ℚ K))).IsPrime)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤ (d : ℝ) ^ 2 := by
  obtain ⟨hdim, hlc⟩ := affineCurve_filteredHilbertPolynomial_degree I d hd hdegree
  simpa only [pow_zero, mul_one] using nonabsolute_variety_count_le_box
    (K := K) (m := 0) I d ⟨hdim, by simpa using hlc⟩ hred hB

end
end CCDN
