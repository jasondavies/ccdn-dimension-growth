/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.CongruencePrimeWindow
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.Surface.PrimeWindowSubpower

/-! The precise subpower scale in Salberger's covering theorem. The number
of prime-window edges and any fixed logarithmic loss are bounded by
B^(c/log(1+log B)), with constants fixed before B. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma log_add_one_sq_le_eight_mul {t : ℝ} (ht : 1 ≤ t) :
    (Real.log (t + 1)) ^ 2 ≤ 8 * t := by
  have hu : 0 < t + 1 := by linarith
  have hl : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hb := log_le_dimension_root (r := 2) (by omega) hu
  have hb' : Real.log (t + 1) ≤ 2 * Real.sqrt (t + 1) := by
    simpa only [Nat.cast_ofNat, ← Real.sqrt_eq_rpow] using hb
  have hs := Real.sq_sqrt hu.le
  nlinarith [Real.sqrt_nonneg (t + 1)]

/-- The prime-window size constant `(log 4 + 4) ρ` is positive. -/
private lemma log_four_add_four_mul_scalingPrimeRatio_pos :
    0 < (Real.log 4 + 4) * scalingPrimeRatio := by
  have hp := scalingPrimeRatio_one_le
  have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  positivity

/-- Large range `log B ≥ 1` of the prime-window rate: with `m` the number of primes in the
congruence window at scale `K (log B + 1)` and `A = (log 4 + 4) ρ`, the edge weight
`(2R)^m (log B + 1)^k` is at most `B^(c / log(log B + 1))` for `c = 2AK log(2R) + 8k + 1`. -/
lemma congruencePrimeWindow_weight_le_rpow {K R B : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ)
    (hB : 1 ≤ B) (hlarge : 1 ≤ Real.log B) :
    (2 * R) ^ (congruencePrimeWindow (K * (Real.log B + 1))).card * (Real.log B + 1) ^ k ≤
      B ^ ((2 * ((Real.log 4 + 4) * scalingPrimeRatio) * K * Real.log (2 * R) + 8 * k + 1) /
        Real.log (Real.log B + 1)) := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := log_four_add_four_mul_scalingPrimeRatio_pos
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogR : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  let c := 2 * A * K * Real.log (2 * R) + 8 * k + 1
  let t := Real.log B
  let L := K * (t + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by dsimp only [L]; nlinarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu : 0 < t + 1 := by linarith
  have hlogpos : 0 < Real.log (t + 1) := Real.log_pos (by linarith)
  have hcard := congruencePrimeWindow_card_log_bound hL
  have hcomp : t + 1 ≤ L := by dsimp only [L]; nlinarith
  have hlogcomp := Real.log_le_log hu hcomp
  have hcard' : (m : ℝ) * Real.log (t + 1) ≤ 2 * A * K * t := by
    have hh := mul_le_mul_of_nonneg_left hlogcomp hm
    change (m : ℝ) * Real.log L ≤ A * L at hcard
    have hscale := mul_le_mul_of_nonneg_left
      (show t + 1 ≤ 2 * t by linarith) (show 0 ≤ A * K by positivity)
    dsimp only [L] at hcard hh
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hcard' hlogR
  have hsecond := mul_le_mul_of_nonneg_left (log_add_one_sq_le_eight_mul hlarge)
    (show 0 ≤ (k : ℝ) by positivity)
  have hmain : (m : ℝ) * Real.log (2 * R) + k * Real.log (t + 1) ≤
      c / Real.log (t + 1) * t := by
    apply (mul_le_mul_iff_of_pos_right hlogpos).mp
    have he : (c / Real.log (t + 1) * t) * Real.log (t + 1) = c * t := by
      field_simp
    rw [he]
    dsimp only [c]
    nlinarith
  apply Real.le_rpow_of_log_le hB0
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  exact hmain

/-- Bounded range `0 ≤ log B ≤ 1` of the prime-window rate: with `m` and `A` as in
`congruencePrimeWindow_weight_le_rpow`, the edge weight `(2R)^m (log B + 1)^k` is at most
`exp(2AK log(2R) / log 2) 2^k`. -/
private lemma congruencePrimeWindow_weight_le_exp {K R B : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ)
    (ht : 0 ≤ Real.log B) (hsmall : Real.log B ≤ 1) :
    (2 * R) ^ (congruencePrimeWindow (K * (Real.log B + 1))).card * (Real.log B + 1) ^ k ≤
      Real.exp (2 * ((Real.log 4 + 4) * scalingPrimeRatio) * K / Real.log 2 *
        Real.log (2 * R)) * 2 ^ k := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := log_four_add_four_mul_scalingPrimeRatio_pos
  have hlogR : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let t := Real.log B
  let L := K * (t + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by dsimp only [L]; nlinarith
  have hu : 0 < t + 1 := by linarith
  have hcard := congruencePrimeWindow_card_log_two hL
  have hm' : (m : ℝ) ≤ 2 * A * K / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    change (m : ℝ) * Real.log 2 ≤ A * L at hcard
    have hscale := mul_le_mul_of_nonneg_left
      (show t + 1 ≤ 2 by linarith) (show 0 ≤ A * K by positivity)
    dsimp only [L] at hcard
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hm' hlogR
  have hpow : (2 * R) ^ m ≤ Real.exp (2 * A * K / Real.log 2 * Real.log (2 * R)) := by
    rw [← Real.exp_log (by positivity : 0 < (2 * R) ^ m), Real.log_pow]
    exact Real.exp_le_exp.mpr hh
  have hpoly : (t + 1) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ hu.le (by linarith) k
  exact mul_le_mul hpow hpoly (by positivity) (by positivity)

/-- The exact logarithmic denominator of CCDN Theorem 4.3.5, including
uniform control of the bounded range starting at B=1. -/
private theorem congruencePrimeWindow_edge_polylog_salberger {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ B : ℝ, 1 ≤ B →
      (congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card *
        (Real.log B + 1) ^ k ≤
          C * B ^ (c / Real.log (1 + Real.log B)) := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := log_four_add_four_mul_scalingPrimeRatio_pos
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlogR : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  let c := 2 * A * K * Real.log (2 * R) + 8 * k + 1
  let C := Real.exp (2 * A * K / Real.log 2 * Real.log (2 * R)) * 2 ^ k + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC1 : 1 ≤ C := by
    have hh : 0 ≤ Real.exp (2 * A * K / Real.log 2 * Real.log (2 * R)) * 2 ^ k := by
      positivity
    dsimp only [C]
    linarith
  refine ⟨C,c,by linarith,hc,?_⟩
  intro B hB
  let m := (congruencePrimeWindow (K * (Real.log B + 1))).card
  have ht : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [add_comm 1 (Real.log B)]
  have hreduce : (m : ℝ) * R ^ m * (Real.log B + 1) ^ k ≤
      (2 * R) ^ m * (Real.log B + 1) ^ k := by
    have hh : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.le_of_lt m.lt_two_pow_self)
    rw [mul_pow]
    gcongr
  apply hreduce.trans
  by_cases hlarge : 1 ≤ Real.log B
  · exact (congruencePrimeWindow_weight_le_rpow hK hR k hB hlarge).trans
      (le_mul_of_one_le_left (by positivity) hC1)
  · have hBpow : 1 ≤ B ^ (c / Real.log (Real.log B + 1)) :=
      Real.one_le_rpow hB (div_nonneg hc.le (Real.log_nonneg (by linarith)))
    calc
      _ ≤ _ := congruencePrimeWindow_weight_le_exp hK hR k ht (le_of_not_ge hlarge)
      _ ≤ C := by dsimp only [C]; linarith
      _ ≤ C * B ^ (c / Real.log (Real.log B + 1)) := le_mul_of_one_le_right (by linarith) hBpow

/-- With `W` the congruence prime window of length `K (log B + 1)`,
`|W| R^|W| B^α (log B + 1)^k ≤ C B^(α + c / log(1 + log B))` for every real exponent `α`. -/
theorem congruencePrimeWindow_edge_polylog_salberger_weight {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ α B : ℝ, 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ α * (Real.log B + 1) ^ k ≤
          C * B ^ (α + c / Real.log (1 + Real.log B)) := by
  obtain ⟨C,c,hC,hc,h⟩ := congruencePrimeWindow_edge_polylog_salberger hK hR k
  refine ⟨C,c,hC,hc,?_⟩
  intro α B hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hh := mul_le_mul_of_nonneg_right (h B hB) (Real.rpow_nonneg hB0.le α)
  rw [Real.rpow_add hB0]
  convert hh using 1 <;> ring

end
end CCDN
