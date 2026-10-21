/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeComparison
public import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
public import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
public import CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightDegree
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceProjectiveAuxiliary
/-! The two positioned auxiliary estimates for the entire bounded projective
zero set. The small-height logarithmic term has coefficient exactly one. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient of the main term in the positioned small-height estimate. -/
def hypersurfaceSmallProjectiveConstant (n : ℕ) (T : ℝ) : ℝ :=
  Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))

/-- The large-height estimate has no dependence on the radius or coefficient height. -/
def hypersurfaceLargeProjectiveConstant (n : ℕ) (T : ℝ) : ℝ :=
  8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) + 2

lemma hypersurfaceSmallProjectiveConstant_pos (n : ℕ) (T : ℝ) :
    0 < hypersurfaceSmallProjectiveConstant n T := by
  unfold hypersurfaceSmallProjectiveConstant
  positivity

lemma hypersurfaceLargeProjectiveConstant_pos (n : ℕ) (T : ℝ) :
    0 < hypersurfaceLargeProjectiveConstant n T := by
  unfold hypersurfaceLargeProjectiveConstant
  positivity

/-- CCDN Lemma 3.3.2 for the full bounded projective zero set, with explicit
position cost and the stronger residual `4*d`. No finite-family input remains. -/
theorem hypersurface_small_height_projective_auxiliary
    {n d : ℕ} (order : MonomialOrder (Fin (n + 3)))
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : AbsolutelyIrreducible f)
    {B : ℝ} (hB : 1 ≤ B) (T : ℝ)
    (hheight : Real.log (integerCoefficientHeight f : ℝ) ≤
      2 * d * (n + 2 : ℝ) * Real.log B)
    (hposition : Real.log (integerCoefficientHeight f : ℝ) ≤
      Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * d * degreeRoot n d) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceSmallProjectiveConstant n T *
          auxMainTerm n d B (hypersurfaceBadPrimeFactor f) (integerCoefficientHeight f) +
        (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + 4 * d ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  have hH : 0 < (integerCoefficientHeight f : ℝ) := by
    exact_mod_cast integerCoefficientHeight_pos f hf0
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  have hlead : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ (integerCoefficientHeight f : ℝ) :=
    coefficient_abs_le_integerCoefficientHeight f (order.degree f)
  obtain ⟨t, z, hprim, hzero, hbox, hlift⟩ := exists_bounded_projective_zero_family f hf B
  obtain ⟨bad, M, hbad, hdegree, g, hg0, hgh, hgz, hgnd⟩ :=
    hypersurface_auxiliary_small_height_degree order f hf hd hir z hprim hzero hB hbox
      ((Real.log_le_log hL hlead).trans hheight)
  have hfactor := hypersurfaceBadPrimeFactor_eq_exp f hir (hf.totalDegree hf0) bad hbad
  have hp := hypersurfaceSmallThreshold_position hd (by linarith : 0 ≤ B) hH hL
    (Real.exp_pos (∑ p ∈ bad, Real.log p / p)).le hposition
  have hp' : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (primeSetFactor bad) ≤ hypersurfaceSmallProjectiveConstant n T *
        auxMainTerm n d B (hypersurfaceBadPrimeFactor f) (integerCoefficientHeight f) := by
    rw [hfactor]
    convert hp using 1
    unfold hypersurfaceSmallProjectiveConstant hypersurfaceSmallThreshold auxMainTerm
    ring
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact ⟨M, by linarith, g, hg0, hgh, hlift g hgh hgz, hgnd⟩

/-- CCDN Lemma 3.3.3 for the full bounded projective zero set. The displayed
constant depends only on dimension and the fixed positioning parameter. -/
theorem hypersurface_large_height_projective_auxiliary
    {n d : ℕ} (order : MonomialOrder (Fin (n + 3)))
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : AbsolutelyIrreducible f)
    {B : ℝ} (hB : 1 ≤ B) (T : ℝ) (hT : 0 ≤ T)
    (hheight : 2 * d * (n + 2 : ℝ) * Real.log B ≤
      Real.log (integerCoefficientHeight f : ℝ))
    (hposition : Real.log (integerCoefficientHeight f : ℝ) ≤
      Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * d * degreeRoot n d) :
    ∃ M : ℕ, (M : ℝ) ≤ hypersurfaceLargeProjectiveConstant n T *
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := by
    exact_mod_cast integerCoefficientHeight_pos f (ne_zero_of_irreducible_map hir)
  obtain ⟨t, z, hprim, hzero, hbox, hlift⟩ := exists_bounded_projective_zero_family f hf B
  obtain ⟨M, hdegree, g, hg0, hgh, hgz, hgnd⟩ :=
    hypersurface_auxiliary_large_height_degree order f hf hd hir
      (integerCoefficientHeight f : ℝ) hH (coefficient_abs_le_integerCoefficientHeight f)
      z hprim hzero hB hbox T hT hheight hposition
  exact ⟨M, hdegree, g, hg0, hgh, hlift g hgh hgz, hgnd⟩

end
end CCDN
