/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A superlinear determinant divisor absorbs the interpolation factorial
uniformly in the rank. -/

@[expose] public section
namespace CCDN
noncomputable section
open Filter

/-- A dimension-only determinant error absorbs the complete factorial term.
The bounded-rank range is included in the constant. -/
theorem exists_determinant_factorial_absorption {c a : ℝ} (hc : 0 < c)
    (ha : 0 < a) (E : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℕ) (G : ℝ), 0 ≤ G →
      c * (s : ℝ) ^ (1 + a) * (Real.log s - E) ≤ G →
      (s : ℝ) * Real.log ((s : ℝ) + 1) ≤ G + C := by
  have he : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ 2 * max E 0 ≤ Real.log x ∧
      4 / c ≤ x ^ a := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * max E 0)),
      (tendsto_rpow_atTop ha).eventually (eventually_ge_atTop (4 / c))] with x hx hl hp
    exact ⟨hx, hl, hp⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp he
  let U := max 2 T
  have hU : 2 ≤ U := le_max_left _ _
  have hU0 : 0 < U := by linarith
  have hlogU : 0 ≤ Real.log (U + 1) := Real.log_nonneg (by linarith)
  refine ⟨U * Real.log (U + 1), mul_nonneg hU0.le hlogU, ?_⟩
  intro s G hG hdiv
  by_cases hs : U ≤ (s : ℝ)
  · obtain ⟨hs2, hl, hp⟩ := hT (s : ℝ) ((le_max_right 2 T).trans hs)
    have hs0 : (0 : ℝ) < s := by linarith
    have hls : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg (by linarith)
    have hE : 2 * E ≤ Real.log s := (mul_le_mul_of_nonneg_left (le_max_left E 0)
      (by norm_num : (0 : ℝ) ≤ 2)).trans hl
    have hcp : 4 ≤ c * (s : ℝ) ^ a := by
      have hh := mul_le_mul_of_nonneg_left hp hc.le
      field_simp at hh
      nlinarith
    have hlog : Real.log ((s : ℝ) + 1) ≤ 2 * Real.log (s : ℝ) := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < (s : ℝ) + 1)
        (show (s : ℝ) + 1 ≤ (s : ℝ) ^ (2 : ℕ) by nlinarith)
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hr : (s : ℝ) ^ (1 + a) = (s : ℝ) * (s : ℝ) ^ a := by
      rw [Real.rpow_add hs0, Real.rpow_one]
    rw [hr] at hdiv
    have h1 := mul_le_mul_of_nonneg_left hlog hs0.le
    have h2 := mul_le_mul_of_nonneg_left (show Real.log s ≤ 2 * (Real.log s - E) by linarith)
      (show 0 ≤ (s : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcp
      (mul_nonneg hs0.le (show 0 ≤ Real.log s - E by linarith))
    nlinarith [mul_nonneg hU0.le hlogU]
  · have hsu : (s : ℝ) ≤ U := le_of_not_ge hs
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (s : ℝ) + 1)
      (show (s : ℝ) + 1 ≤ U + 1 by linarith)
    have hm := mul_le_mul hl hsu (by positivity : (0 : ℝ) ≤ s) hlogU
    nlinarith

end
end CCDN
