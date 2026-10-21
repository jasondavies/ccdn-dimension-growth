/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.LogarithmicSalbergerRate
/-! Numerical normalization of the curve count and the exceptional-set
bound in the literal surface covering theorem. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem salberger_curve_number_normalization {α B : ℝ}
    (hα : α ≤ 1) (hB : 1 ≤ B) :
    B ^ α * (Real.log B + 1) ≤ 2 * (B ^ α * Real.log B + 1) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hp : 0 < B ^ α := Real.rpow_pos_of_pos hB0 _
  have hl := Real.one_sub_inv_le_log_of_pos hp
  rw [Real.log_rpow hB0] at hl
  have hαlog := mul_le_mul_of_nonneg_right hα (Real.log_nonneg hB)
  have hmain := mul_le_mul_of_nonneg_left (hl.trans hαlog) hp.le
  have hinv : B ^ α * (B ^ α)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  nlinarith

lemma salberger_nonnegative_weight_mono {α B : ℝ} (hα : 0 ≤ α) (hB : 1 ≤ B) :
    B ^ α * (Real.log B + 1) ≤ B ^ (2 * α) * (Real.log B + 1) ^ 4 := by
  have hlog : 1 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB]
  apply mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
    (by simpa only [pow_one] using pow_le_pow_right₀ hlog (by omega : 1 ≤ 4))
  · positivity
  · positivity

theorem salberger_remainders_combine (E R c₀ : ℝ)
    (hE : 0 ≤ E) (hR : 0 ≤ R) (hc₀ : 0 < c₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ α B : ℝ, 1 ≤ B →
      E * B ^ α * (Real.log B + 1) ^ 4 +
        R * B ^ (α + c₀ / Real.log (1 + Real.log B)) ≤
          C * B ^ (α + c / Real.log (1 + Real.log B)) := by
  refine ⟨17 * E + R + 1, c₀ + 33, by positivity, by positivity, ?_⟩
  intro α B hB
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden : 0 ≤ Real.log (1 + Real.log B) := Real.log_nonneg (by linarith [Real.log_nonneg hB])
  have hpoly := logarithm_add_one_pow_salberger 4 hB
  norm_num at hpoly
  have hexp1 : 33 / Real.log (1 + Real.log B) ≤
      (c₀ + 33) / Real.log (1 + Real.log B) :=
    div_le_div_of_nonneg_right (by linarith) hden
  have hexp2 : c₀ / Real.log (1 + Real.log B) ≤
      (c₀ + 33) / Real.log (1 + Real.log B) :=
    div_le_div_of_nonneg_right (by linarith) hden
  have hp1 : E * B ^ α * (Real.log B + 1) ^ 4 ≤
      (17 * E) * B ^ (α + (c₀ + 33) / Real.log (1 + Real.log B)) := by
    calc
      _ ≤ E * B ^ α * (17 * B ^ (33 / Real.log (1 + Real.log B))) := by gcongr
      _ = 17 * E * B ^ (α + 33 / Real.log (1 + Real.log B)) := by
        rw [Real.rpow_add hB0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by positivity)
  have hp2 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hB (add_le_add_left hexp2 α)) hR
  have hp2' : R * B ^ (α + c₀ / Real.log (1 + Real.log B)) ≤
      R * B ^ (α + (c₀ + 33) / Real.log (1 + Real.log B)) := by
    simpa only [add_comm] using hp2
  have hp : 0 ≤ B ^ (α + (c₀ + 33) / Real.log (1 + Real.log B)) := by positivity
  nlinarith

end
end CCDN
