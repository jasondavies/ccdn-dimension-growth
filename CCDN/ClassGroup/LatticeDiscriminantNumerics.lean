/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Algebra

/-! Numerical conversion of a lattice norm-product bound into the uniform
discriminant-root scale for its largest minimum. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem largest_minimum_le_discriminant_root
    {n : ℕ} (hn : 0 < n) {M P D : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hminimum : M ^ n ≤ P ^ 2)
    (hproduct : P ≤ Real.sqrt n * (n : ℝ) ^ n * Real.sqrt D) :
    M ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := (sq_le_sq₀ hP (by positivity)).mpr hproduct
  have hsq' : P ^ 2 ≤ (n : ℝ) ^ (2 * n + 1) * D := by
    convert hsq using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt hD,
      pow_succ, pow_mul]
    ring
  have hdegrees : (n : ℝ) ^ (2 * n + 1) ≤ (n : ℝ) ^ (3 * n) :=
    pow_le_pow_right₀ hn1 (by omega)
  have hroot : (D ^ (1 / (n : ℝ))) ^ n = D := by
    rw [← Real.rpow_mul_natCast hD, one_div_mul_cancel hnR.ne', Real.rpow_one]
  apply le_of_pow_le_pow_left₀ hn.ne' (by positivity)
  rw [mul_pow, ← pow_mul, hroot]
  exact hminimum.trans (hsq'.trans (mul_le_mul_of_nonneg_right hdegrees hD))

theorem sqrt_degree_le_discriminant_root
    {n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 1 ≤ D) :
    Real.sqrt n ≤ (n : ℝ) ^ 3 * D ^ (1 / (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≤ (n : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg n)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hn1 (by omega : 1 ≤ 3)
  have hroot : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD (by positivity)
  exact (hsqrt.trans hcube).trans
    (by simpa using mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (n : ℝ) ^ 3))

end
end CCDN
