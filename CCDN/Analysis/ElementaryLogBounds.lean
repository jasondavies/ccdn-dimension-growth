/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! Elementary uniform bounds for the real logarithm. -/

@[expose] public section
namespace CCDN

/-- The logarithm `log (1 + x)` exceeds `x / 4` by at most `log 4 + 1` for `x ≥ 0`. -/
lemma log_one_add_sub_quarter_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + x) / 4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

end CCDN
