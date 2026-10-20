module

public import AffineCurveCounting.AuxiliaryRatioEstimates

/-! In the large-height range, the coefficient saving absorbs the radius
and leaves a negative logarithmic-height term to control the bad-prime factor. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

lemma auxiliary_large_height_bracket_bound {r d M X a k u b l h T : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 8 * d * (r + 1) ≤ M) (hX : 0 < X)
    (halow : X * (M - d) / ((r + 1) * M) ≤ a)
    (haup : a ≤ X * (M + r) / ((r + 1) * M))
    (hk : 0 ≤ k) (hklow : 1 / (d * (r + 1)) - 1 / M ≤ k)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hT : 0 ≤ T)
    (hheight : 2 * d * (r + 1) * b ≤ h) (hposition : h ≤ l + T * d * X)
    (hcomparison : a * u ≤ b - k * l) :
    u ≤ T - h / (8 * d * X) := by
  have hd0 : 0 < d := by linarith
  have hM2 : 2 * d ≤ M := by nlinarith [mul_nonneg hd0.le hr]
  have hM0 : 0 < M := by linarith
  obtain ⟨ha, hrecip⟩ := auxiliary_reciprocal_bound hr hd hM2 hX halow
  have hquot := auxiliary_kernel_quotient_bound hr hd hM0 hX ha hk haup hklow
  have hrecip' : 1 / a ≤ 5 * (r + 1) / (4 * X) := by
    apply hrecip.trans
    field_simp
    nlinarith [mul_nonneg hd0.le hr, mul_nonneg hr (sub_nonneg.mpr hM)]
  have hquot' : 3 / (4 * d * X) ≤ k / a := by
    apply le_trans _ hquot
    field_simp
    nlinarith [mul_nonneg hd0.le hr]
  have hu : u ≤ b / a - (k / a) * l := by
    have hh := (le_div_iff₀ ha).mpr (by nlinarith [hcomparison] : u * a ≤ b - k * l)
    convert hh using 1
    ring
  have hb' : b / a ≤ (5 * (r + 1) / (4 * X)) * b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      mul_le_mul_of_nonneg_right hrecip' hb
  have hl' := mul_le_mul_of_nonneg_right hquot' hl
  have hu' : u ≤ (5 * (r + 1) / (4 * X)) * b - (3 / (4 * d * X)) * l := by linarith
  have he : (5 * (r + 1) / (4 * X)) * b - (3 / (4 * d * X)) * l =
      (10 * d * (r + 1) * b - 6 * l) / (8 * d * X) := by field_simp; ring
  rw [he] at hu'
  have hden : 0 < 8 * d * X := by positivity
  have hmul := (le_div_iff₀ hden).mp hu'
  apply (le_of_mul_le_mul_right ?_ hden)
  have he' : (T - h / (8 * d * X)) * (8 * d * X) = T * (8 * d * X) - h := by field_simp
  rw [he']
  nlinarith [mul_nonneg (mul_nonneg hT hd0.le) hX.le]

/-- A logarithmic bad-prime loss is absorbed by a linear height saving. -/
lemma log_one_add_le_linear_add_log {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) :
    Real.log (1 + x) ≤ x / c + Real.log c := by
  have hc0 : 0 < c := by linarith
  have hp : 0 < (1 + x) / c := by positivity
  have hh := Real.log_le_sub_one_of_pos hp
  rw [Real.log_div (by positivity) hc0.ne'] at hh
  have hdiv : 1 / c ≤ 1 := (div_le_one hc0).mpr hc
  have he : (1 + x) / c = 1 / c + x / c := by ring
  rw [he] at hh
  linarith

end
end AffineCurveCounting
