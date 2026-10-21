/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.PlaneSectionSum
/-! Numerical absorption of bad and zero plane sections above the cutoff
p>27*d^4. The leading term remains exactly p^(m-1). -/

@[expose] public section
namespace CCDN
noncomputable section

lemma hypersurface_bad_section_error {d p : ℝ} (hd : 1 ≤ d) (hp : 27 * d ^ 4 < p) :
    2 * d ^ 4 * p + d ^ 3 ≤ 3 * d ^ 2 * p * Real.sqrt p := by
  have hd0 : 0 ≤ d := by linarith
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hd4 : 1 ≤ d ^ 4 := by nlinarith [sq_nonneg (d ^ 2 - 1)]
  have hp1 : 1 ≤ p := by nlinarith
  have hp0 : 0 ≤ p := by linarith
  have hs : d ^ 2 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (d ^ 2)])
  have hds : d ≤ Real.sqrt p := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * d ^ 2 * p by positivity)
  have h2 := mul_le_mul_of_nonneg_left hds (sq_nonneg d)
  have h3 := mul_le_mul_of_nonneg_right hp1 (show 0 ≤ d ^ 2 * Real.sqrt p by positivity)
  nlinarith

/-- The unsimplified incidence estimate implies the desired sharp affine
hypersurface estimate in every ambient dimension at least three. -/
theorem hypersurface_count_of_incidence_bound (n : ℕ) {d p N : ℝ}
    (hd : 1 ≤ d) (hp : 27 * d ^ 4 < p)
    (hcount : N * p ^ (2 * n + 8) ≤
      p ^ (3 * n + 9) * (p + 161 * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * p ^ (3 * n + 9) + d ^ 3 * p ^ (3 * n + 8)) :
    N ≤ p ^ (n + 2) + 164 * d ^ 2 * p ^ (n + 1) * Real.sqrt p := by
  have hp0 : 0 < p := lt_of_le_of_lt (by positivity) hp
  have herr := hypersurface_bad_section_error hd hp
  have hmajor := mul_le_mul_of_nonneg_left herr (pow_nonneg hp0.le (3 * n + 8))
  have hfact :
      p ^ (3 * n + 9) * (p + 161 * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * p ^ (3 * n + 9) + d ^ 3 * p ^ (3 * n + 8) ≤
      p ^ (3 * n + 8) * (p ^ 2 + 164 * d ^ 2 * p * Real.sqrt p) := by
    rw [show 3 * n + 9 = (3 * n + 8) + 1 by omega, pow_succ]
    nlinarith
  have he : p ^ (3 * n + 8) * (p ^ 2 + 164 * d ^ 2 * p * Real.sqrt p) =
      (p ^ (n + 2) + 164 * d ^ 2 * p ^ (n + 1) * Real.sqrt p) * p ^ (2 * n + 8) := by
    rw [show 3 * n + 8 = (2 * n + 8) + n by omega, pow_add]
    simp only [pow_add, pow_one]
    ring
  rw [he] at hfact
  exact (mul_le_mul_iff_left₀ (pow_pos hp0 _)).mp (hcount.trans hfact)

end
end CCDN
