module

public import CCDN.HypersurfaceRankProfile

/-! Exact leading term for the dimension root of the homogeneous Hilbert rank. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Taking the dimension root preserves the factorial leading coefficient. -/
theorem hypersurface_rank_root_bounds {r d M s : ℕ} (hrpos : 0 < r) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) - d + 1) ≤
        (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ∧
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ≤
        (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) + r) := by
  obtain ⟨hl, hu⟩ := hypersurface_rank_power_bounds hdM hr
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hmd : (0 : ℝ) ≤ (M : ℝ) - d + 1 := by
    have : (d : ℝ) ≤ M := by exact_mod_cast hdM
    linarith
  have hl' := (div_le_iff₀ hfac).mp hl
  have hu' := (le_div_iff₀ hfac).mp hu
  have hlroot := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hmd r)) hl'
    (show 0 ≤ 1 / (r : ℝ) by positivity)
  have huroot := Real.rpow_le_rpow
    (mul_nonneg (Nat.cast_nonneg s) hfac.le) hu' (show 0 ≤ 1 / (r : ℝ) by positivity)
  rw [Real.mul_rpow (Nat.cast_nonneg d) (pow_nonneg hmd r),
    Real.mul_rpow (Nat.cast_nonneg s) hfac.le, one_div,
    Real.pow_rpow_inv_natCast hmd hrpos.ne'] at hlroot
  rw [Real.mul_rpow (Nat.cast_nonneg s) hfac.le,
    Real.mul_rpow (Nat.cast_nonneg d) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) hrpos.ne'] at huroot
  constructor
  · simpa only [one_div, mul_comm] using hlroot
  · simpa only [one_div, mul_comm] using huroot

/-- Uniform O_r(d²) error with an explicit dimension constant; the leading
coefficient is exactly d^(1/r), not a fixed-factor approximation. -/
theorem hypersurface_rank_root_error {r d M s : ℕ} (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    |(r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) -
      (d : ℝ) ^ (1 / (r : ℝ)) * M| ≤ (r + 1 : ℝ) * (d : ℝ) ^ 2 := by
  obtain ⟨hl, hu⟩ := hypersurface_rank_root_bounds hrpos hdM hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  have hroot : (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
    calc
      _ ≤ (d : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 ((div_le_one (by linarith)).mpr hr1)
      _ = _ := Real.rpow_one _
  have hroot0 : 0 ≤ (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  have hlow := mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg d)
  have hhigh := mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg r)
  have hdr : (d : ℝ) * r ≤ (r : ℝ) * (d : ℝ) ^ 2 := by
    have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hdd (Nat.cast_nonneg r)]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg r) (sq_nonneg (d : ℝ))]

/-- The normalized root has uniform error O_r(d²/M). -/
theorem hypersurface_rank_normalized_root_error {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    |(r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / M -
      (d : ℝ) ^ (1 / (r : ℝ))| ≤ (r + 1 : ℝ) * (d : ℝ) ^ 2 / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have h := div_le_div_of_nonneg_right (hypersurface_rank_root_error hrpos hd hdM hr) hM.le
  calc
    _ = |((r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) -
        (d : ℝ) ^ (1 / (r : ℝ)) * M) / M| := by
      congr 1
      field_simp
    _ = |(r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) -
        (d : ℝ) ^ (1 / (r : ℝ)) * M| / M := by rw [abs_div, abs_of_pos hM]
    _ ≤ _ := h

end
end CCDN
