/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AffineHypersurfaceAuxiliary
/-! The coefficient-sensitive affine plane count obtained from the full
auxiliary theorem and Bezout. The bad-prime factor is the defined geometric
factor, including degree-dropping reductions; the literal printed affine
factor in CCDN has a separate statement issue. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The complete minimum expression in the affine plane count. -/
def affinePlaneCoefficientCountExpression (d : ℕ) (B L b : ℝ) : ℝ :=
  B ^ (1 / (d : ℝ)) *
      min ((d : ℝ) ^ 2 * Real.log L + (d : ℝ) ^ 3 * Real.log B + (d : ℝ) ^ 4)
        ((d : ℝ) ^ 4 * b) / L ^ (1 / (d : ℝ) ^ 2) +
    d * Real.log B + (d : ℝ) ^ 4

theorem degree_mul_affineAuxiliaryDegreeExpression (d : ℕ) (B L b : ℝ) :
    (d : ℝ) * affineAuxiliaryDegreeExpression 0 d B L b =
      affinePlaneCoefficientCountExpression d B L b := by
  have hmin :
      min ((d : ℝ) ^ 2 * Real.log L + (d : ℝ) ^ 3 * Real.log B + (d : ℝ) ^ 4)
        ((d : ℝ) ^ 4 * b) =
      (d : ℝ) ^ 2 *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
    rw [mul_min_of_nonneg _ _ (sq_nonneg (d : ℝ))]
    congr 1 <;> ring
  unfold affineAuxiliaryDegreeExpression affinePlaneCoefficientCountExpression
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero,
    one_mul, sub_self, mul_one, show (2 - 1 : ℝ) = 1 by norm_num,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  rw [hmin]
  ring_nf

end
end CCDN
