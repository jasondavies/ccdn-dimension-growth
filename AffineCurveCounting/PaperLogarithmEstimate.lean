module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The exact elementary logarithmic estimate used in CCDN Lemma 3.3.5. -/

@[expose] public section
namespace AffineCurveCounting

/-- CCDN Lemma 3.3.5, with its absolute additive constant sharpened to -1. -/
theorem log_log_sub_div_le {c x : ℝ} (hc : 0 < c) (hx : 1 < x) :
    Real.log (Real.log x) - Real.log x / c ≤ Real.log c - 1 := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hh := Real.log_le_sub_one_of_pos (div_pos hlog hc)
  rw [Real.log_div hlog.ne' hc.ne'] at hh
  linarith

end AffineCurveCounting
