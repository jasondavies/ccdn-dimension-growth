/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.ScalingPrime
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Height.ScaledBoxExponent
/-! The affine exponent 1/d with the scaling prime constructed from Mertens.
This branch assumes a nonzero constant coefficient of small logarithmic height;
the sharp finite-field count is an explicit geometric hypothesis. -/

@[expose] public section
namespace CCDN
open Real

theorem plane_finite_count_small_constant_coefficient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) (hf0 : f.coeff 0 ≠ 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0)
    {B C : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio)
    (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤
      (38 + 8 * Real.exp (heightDeterminantError C + 20) +
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio) *
      (f.totalDegree : ℝ) ^ 3 * B ^ (1 / (f.totalDegree : ℝ)) *
        (Real.log B + f.totalDegree) := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hf0 hheight
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hBp : B ≤ scalingPrimeRatio * p := by
    have h := (div_lt_iff₀ hA0).mp hlo
    nlinarith
  exact scaled_plane_finite_count_one_over_degree f hprim hir hd hp hnd z hinj
    ⟨hA.trans hB, hz, hbox⟩ hA hhi hBp hC hcount

end CCDN
