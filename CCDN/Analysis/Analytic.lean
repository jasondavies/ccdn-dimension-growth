/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Uniform estimates and bounded-degree consequences

Real inequalities used to deduce uniform and bounded-degree estimates from CCDN
Corollary 4.2.4.
-/

@[expose] public section

namespace CCDN

/-- Absorb the logarithm with a specified positive exponent loss and an explicit constant. -/
theorem sqrt_log_le_rpow {B ε D : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) (hD : 0 ≤ D) :
    B ^ (1 / 2 : ℝ) * (Real.log B + D) ≤
      (1 / ε + D) * B ^ (1 / 2 + ε : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hp1 : 1 ≤ B ^ ε := Real.one_le_rpow hB hε.le
  have hl := Real.log_le_rpow_div hB0.le hε
  have hd := mul_le_mul_of_nonneg_left hp1 hD
  have hsum : Real.log B + D ≤ (1 / ε + D) * B ^ ε := by
    rw [div_eq_mul_inv] at hl
    simp only [one_div]
    nlinarith
  calc
    _ ≤ B ^ (1 / 2 : ℝ) * ((1 / ε + D) * B ^ ε) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _)
    _ = _ := by rw [Real.rpow_add hB0]; ring

end CCDN
