module

public import AffineCurveCounting.PrimeWindowSalbergerRate

/-! Fixed logarithmic powers fit the precise exceptional-set exponent
of the surface covering theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

theorem logarithm_add_one_pow_salberger (k : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    (Real.log B + 1) ^ k ≤ (2 ^ k + 1 : ℝ) *
      B ^ ((8 * k + 1 : ℝ) / Real.log (1 + Real.log B)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let t := Real.log B
  have ht : 0 ≤ t := Real.log_nonneg hB
  have hu : 0 < t + 1 := by linarith
  have hlogu : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hden : Real.log (1 + Real.log B) = Real.log (t + 1) := by congr 1; dsimp [t]; ring
  rw [hden]
  by_cases ht1 : 1 ≤ t
  · have hlogpos : 0 < Real.log (t + 1) := Real.log_pos (by linarith)
    have hsq := mul_le_mul_of_nonneg_left (log_add_one_sq_le_eight_mul ht1)
      (show (0 : ℝ) ≤ k by positivity)
    have hlog : (k : ℝ) * Real.log (t + 1) ≤
        (8 * k + 1 : ℝ) / Real.log (t + 1) * t := by
      apply (mul_le_mul_iff_of_pos_right hlogpos).mp
      have he : ((8 * k + 1 : ℝ) / Real.log (t + 1) * t) *
          Real.log (t + 1) = (8 * k + 1 : ℝ) * t := by field_simp
      rw [he]
      nlinarith
    have hp : (t + 1) ^ k ≤ B ^ ((8 * k + 1 : ℝ) / Real.log (t + 1)) := by
      apply Real.le_rpow_of_log_le hB0
      rw [Real.log_pow]
      exact hlog
    exact hp.trans (le_mul_of_one_le_left (by positivity) (by
      have hh : (0 : ℝ) ≤ 2 ^ k := by positivity
      linarith))
  · have ht1' : t ≤ 1 := le_of_lt (lt_of_not_ge ht1)
    have hp : (t + 1) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ hu.le (by linarith) k
    have hBpow : 1 ≤ B ^ ((8 * k + 1 : ℝ) / Real.log (t + 1)) :=
      Real.one_le_rpow hB (by positivity)
    exact hp.trans ((show (2 : ℝ) ^ k ≤ 2 ^ k + 1 by linarith).trans
      (le_mul_of_one_le_right (by positivity) hBpow))

end
end AffineCurveCounting
