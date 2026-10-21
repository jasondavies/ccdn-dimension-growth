module

public import CCDN.PlaneAuxiliaryLargeHeight

/-! Explicit integer degree choices for both coefficient-height ranges. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma auxiliary_integer_degree_selection (d : ℕ) {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · have h := Nat.le_ceil l
    push_cast
    linarith [show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌊R⌋₊ by positivity]
  · have h := Nat.lt_floor_add_one R
    push_cast
    linarith [show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌈l⌉₊ by positivity]
  · have hc := Nat.ceil_lt_add_one hl
    have hf := Nat.floor_le hR
    push_cast
    linarith

end
end CCDN
