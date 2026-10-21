/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Uniform comparison of logarithmic coefficient-height ratios. -/

@[expose] public section
namespace CCDN

lemma weighted_exp_ratio_le {u v a r : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 0 < a) (hr : 1 ≤ r) (hra : 1 ≤ r * a) :
    (v + a) / Real.exp v ≤ r * ((u + a) / Real.exp u) := by
  have ht : 0 ≤ v - u := sub_nonneg.mpr huv
  have hru : 1 ≤ r * (u + a) := by nlinarith
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh : v + a ≤ r * (u + a) * Real.exp (v - u) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ u + a by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hru) ht
    have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ r * (u + a) by positivity)
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).mpr
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hh'
  exact hh'

/-- Replace an upper height by any lower height with a dimension-only loss. -/
theorem logarithmic_height_ratio_le {H Y q c r : ℝ}
    (hY : 1 ≤ Y) (hYH : Y ≤ H) (hq : 0 < q) (hc : 0 < c)
    (hr : 1 ≤ r) (hrqc : 1 ≤ r * (q * c)) :
    (Real.log H + c) / H ^ q ≤ r * ((Real.log Y + c) / Y ^ q) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hu : 0 ≤ q * Real.log Y := mul_nonneg hq.le (Real.log_nonneg hY)
  have huv : q * Real.log Y ≤ q * Real.log H :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYH) hq.le
  have hh := weighted_exp_ratio_le hu huv (mul_pos hq hc) hr hrqc
  rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hY0]
  apply (mul_le_mul_iff_right₀ hq).mp
  rw [mul_comm (Real.log H) q, mul_comm (Real.log Y) q]
  convert hh using 1 <;> ring

end CCDN
