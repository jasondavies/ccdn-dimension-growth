/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.HypersurfacePositionHeight
/-! The box enlargement by d+1 costs only a dimension constant in the
auxiliary degree, with no added power of d in its leading term. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma auxiliary_box_rpow_factor {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    ((d : ℝ) + 1) ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (((r : ℝ) + 1) ^ 2 / r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  rw [Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (log_nat_add_one_le_root hr hd)
    (show 0 ≤ ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) by positivity)
  convert hh using 1
  field_simp

lemma auxiliary_box_log_cost {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log ((d : ℝ) + 1) ≤ ((r : ℝ) + 1) * d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_left (log_nat_add_one_le_root hr hd)
    (Real.rpow_nonneg hd0.le (1 - 1 / (r : ℝ)))
  have he : (d : ℝ) ^ (1 - 1 / (r : ℝ)) * (d : ℝ) ^ (1 / (r : ℝ)) = d := by
    rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  calc
    _ ≤ _ := hh
    _ = ((r : ℝ) + 1) * d := by rw [← mul_left_comm, he]

end
end CCDN
