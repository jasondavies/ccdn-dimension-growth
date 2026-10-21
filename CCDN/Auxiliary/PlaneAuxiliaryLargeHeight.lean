/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.Auxiliary.PlaneAuxiliaryDegree
/-! The complementary large-coefficient-height auxiliary-degree estimate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Real

lemma log_one_add_sub_quarter_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + x) / 4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

set_option maxHeartbeats 800000 in
/-- When the coefficient height exceeds B^(4d), a degree at least 32d
satisfying the no-auxiliary comparison is bounded by a constant times d³.
The constant includes the loss in positioning the leading coefficient. -/
theorem plane_auxiliary_large_height_log_bound {s d M : ℕ} {B L H T K : ℝ}
    (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log L + T * (d : ℝ) ^ 2)
    (hcomparison : (s : ℝ) ^ 2 / 2 *
        (Real.log s - 4 * Real.log d - Real.log (1 + Real.log H / (d : ℝ) ^ 2) - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d := by
  let A := 1 + Real.log H / (d : ℝ) ^ 2
  change _ ≤ _ at hcomparison
  have hdM : d ≤ M := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hdMR : (d : ℝ) ≤ M := by exact_mod_cast hdM
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have he : 2 * (s : ℝ) + (d : ℝ) ^ 2 = d * (2 * M + 3) := by exact_mod_cast hr
  have hslo : (d : ℝ) * M ≤ 2 * s := by nlinarith
  have hshi : (s : ℝ) ≤ d * (M + 1) := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hsquare : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 2 * ((2 + M).choose M) := by
    have hsq := pow_le_pow_left₀ hsR.le hshi 2
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (show 0 ≤ (M : ℝ) + 1 by positivity)]
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have harch := plane_rank_archimedean_error hd hdM hr
  have hbasic : Real.log s - 4 * Real.log d - Real.log A - K ≤
      5 + 2 * M / s * Real.log B -
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
    have hc : Real.log s - 4 * Real.log d - Real.log A - K ≤
        (Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) /
            ((s : ℝ) ^ 2 / 2) := (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 / 2 by positivity)).mpr
      (by simpa only [mul_comm] using hcomparison)
    calc
      _ ≤ _ := hc
      _ ≤ (5 * (s : ℝ) ^ 2 / 2 + s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log L) / ((s : ℝ) ^ 2 / 2) := by
        gcongr
      _ = _ := by field_simp

  have hMlargeR : 32 * (d : ℝ) ≤ M := by exact_mod_cast hMlarge
  have hslarge : 16 * (d : ℝ) ^ 2 ≤ s := by nlinarith
  have hboxrat : 2 * (M : ℝ) / s ≤ (5 / 2 : ℝ) / d := by
    apply (div_le_iff₀ hsR).mpr
    field_simp
    nlinarith
  have hcoefrat : (7 / 8 : ℝ) / (d : ℝ) ^ 2 ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
    have hrat : 1 / (d : ℝ) ^ 2 - 2 / s ≤
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).mpr
      field_simp
      nlinarith
    have hrem : 2 / (s : ℝ) ≤ (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by
      apply (div_le_iff₀ hsR).mpr
      field_simp
      nlinarith
    have hid : (7 / 8 : ℝ) / (d : ℝ) ^ 2 =
        1 / (d : ℝ) ^ 2 - (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by ring
    linarith only [hrat, hrem, hid]
  have hbox : 2 * (M : ℝ) / s * Real.log B ≤
      5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hboxrat hlogB
    have hh' : (5 / 2 : ℝ) / d * Real.log B ≤
        5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
      field_simp
      nlinarith
    exact hh.trans hh'
  have hcoef : 7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
    have hh := mul_le_mul_of_nonneg_right hcoefrat hlogL
    have hh' : 7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
        (7 / 8 : ℝ) / (d : ℝ) ^ 2 * Real.log L := by
      field_simp
      nlinarith
    exact hh'.trans hh
  have hlogs : Real.log d + Real.log M - Real.log 2 ≤ Real.log s := by
    have h := Real.log_le_log (show (0 : ℝ) < d * M / 2 by positivity)
      (show (d : ℝ) * M / 2 ≤ s by linarith)
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hdR.ne' hMR.ne'] at h
  have hlogH := Real.log_nonneg hH
  have hlogA := log_one_add_sub_quarter_le (show 0 ≤ Real.log H / (d : ℝ) ^ 2 by positivity)
  dsimp only [A] at hbasic
  linarith

lemma plane_large_degree_bound_of_log_bound {d M : ℕ} {T K : ℝ}
    (hd : 0 < d) (hM : 0 < M)
    (hlog : Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d) :
    (M : ℝ) ≤ 8 * Real.exp (K + 6 + T) * (d : ℝ) ^ 3 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Real.log_le_log_iff hMR (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
  have h8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  rw [h8]
  convert hlog using 1
  push_cast
  ring

end
end CCDN
