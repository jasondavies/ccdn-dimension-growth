/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.ScalingPrime
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.CountingHypotheses
public import CCDN.Height.PrimitiveIntegerPolynomial
public import CCDN.Statements
import CCDN.Auxiliary.UnscaledModelCount
import CCDN.Height.AffineBoxRanges
import CCDN.Plane.ScaledPlaneSmallCoefficient
/-! Combining the scaling-prime, large-coefficient and small-box branches.
The plane theorem assumes the sharp finite-field count and a nonzero
constant term; a later translation removes the second hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

def affineSmallBoxScale : ℝ := (12 * scalingPrimeRatio) ^ 2

lemma affineSmallBoxScale_one_le : 1 ≤ affineSmallBoxScale := by
  have h := scalingPrimeRatio_one_le
  unfold affineSmallBoxScale
  nlinarith

/-- The constant of `plane_finite_count_nonzero_constant` for residue constant `C`, the sum of
the constants of its regimes, with `E = heightDeterminantError C`: the scaled small-coefficient
regime (`plane_finite_count_small_constant_coefficient`) costs
`38 + 8 exp (E + 20) + 2 exp (E + 23) e¹⁴ e² · scalingPrimeRatio`, and the small-box regime
(`small_box_unscaled_degree_bound`) costs `log S + 6 + 2 exp (E + 23) e¹⁴ exp (2 log S + 6)`
with `S = affineSmallBoxScale`. The large-coefficient constant `34 + 8 exp (E + 20)` is
dominated by the first. The numerical constants are explained in
`projectivePlaneAbsoluteConstant`. -/
def affineNonzeroConstantBound (C : ℝ) : ℝ :=
  (38 + 8 * Real.exp (heightDeterminantError C + 20) +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio) +
  (Real.log affineSmallBoxScale + 6 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
    Real.exp (2 * Real.log affineSmallBoxScale + 6))

lemma affineNonzeroConstantBound_pos (C : ℝ) : 0 < affineNonzeroConstantBound C := by
  have hA : 0 < scalingPrimeRatio := zero_lt_one.trans_le scalingPrimeRatio_one_le
  have hS := Real.log_nonneg affineSmallBoxScale_one_le
  unfold affineNonzeroConstantBound
  positivity

lemma degree_four_le_curveBound {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ 4 ≤ curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hB
  have hp : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hh : (d : ℝ) ≤ B ^ (1 / (d : ℝ)) * (Real.log B + d) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg hd0.le 3)
  unfold curveBound
  nlinarith only [ht]

/-- Coefficient-uniform affine plane count for nonzero constant term and every
B>=1. -/
theorem plane_finite_count_nonzero_constant
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) (hf0 : f.coeff 0 ≠ 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) {B C : ℝ} (hzB : IsBoxZeroFamily f B z)
    (hC : 0 ≤ C) (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ affineNonzeroConstantBound C * curveBound f.totalDegree B := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let K₁ := 38 + 8 * Real.exp (heightDeterminantError C + 20) +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio
  let K₂ := Real.log affineSmallBoxScale + 6 +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp (2 * Real.log affineSmallBoxScale + 6)
  let K₃ := 34 + 8 * Real.exp (heightDeterminantError C + 20)
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by
    have := Real.log_nonneg affineSmallBoxScale_one_le
    dsimp [K₂]
    positivity
  have hK₃ : 0 ≤ K₃ := by dsimp [K₃]; positivity
  have h31 : K₃ ≤ K₁ := by
    have hh : 0 ≤ 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio := by positivity
    dsimp [K₃, K₁]
    linarith
  have hpow := degree_four_le_curveBound hd hB
  have hG : 0 ≤ curveBound d B := (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4).trans hpow
  have hsum : affineNonzeroConstantBound C = K₁ + K₂ := rfl
  rw [hsum]
  by_cases hsmallB : B ≤ affineSmallBoxScale * (d : ℝ) ^ 2
  · have hh := unscaled_plane_finite_count f hprim hir hd z hinj ⟨hB, hz, hbox⟩ hC hcount
    have hs := small_box_unscaled_degree_bound hd affineSmallBoxScale_one_le hB hsmallB (C := C)
    apply hh.trans
    apply max_le
    · apply hs.trans
      have ht := mul_le_mul_of_nonneg_left hpow hK₂
      exact ht.trans (mul_le_mul_of_nonneg_right (by linarith) hG)
    · exact (mul_le_mul_of_nonneg_left hpow hK₃).trans
        (mul_le_mul_of_nonneg_right (by linarith) hG)
  · have hlargeB : (12 * scalingPrimeRatio) ^ 2 * (d : ℝ) ^ 2 ≤ B := (lt_of_not_ge hsmallB).le
    by_cases hsmallH : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · have hBA : scalingPrimeRatio ≤ B := by
        have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hd2 (sq_nonneg (12 * scalingPrimeRatio))]
      have hh := plane_finite_count_small_constant_coefficient f hprim hir hd hf0 z hinj hz hBA
        hsmallH hbox hC hcount
      have ht : (t : ℝ) ≤ K₁ * curveBound d B := by
        convert hh using 1
        simp only [K₁, curveBound, d]
        ring
      exact ht.trans (mul_le_mul_of_nonneg_right (by linarith) hG)
    · have hheight := (large_box_height_threshold hd hA hlargeB).trans (le_of_not_gt hsmallH)
      have hh := unscaled_plane_finite_count_large_coefficient f hprim hir hd z hinj
        ⟨hB, hz, hbox⟩ hC 0 hf0 hheight hcount
      exact hh.trans ((mul_le_mul_of_nonneg_left hpow hK₃).trans
        (mul_le_mul_of_nonneg_right (by linarith) hG))

end
end CCDN
