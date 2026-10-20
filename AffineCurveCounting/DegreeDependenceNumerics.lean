module

public import Mathlib

/-! Numerical obstructions to replacing a positive degree factor by a
little-oh quantity. These lemmas will be applied to constructed point counts. -/

@[expose] public section
namespace AffineCurveCounting
open Filter Asymptotics

theorem not_isLittleO_of_eventually_lower_bound {α : Type*}
    {l : Filter α} [l.NeBot] {f g : α → ℝ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hf : ∀ᶠ x in l, 0 < f x)
    (hbound : ∀ᶠ x in l, c * f x ≤ C * g x) :
    ¬ g =o[l] f := by
  intro h
  have heps : 0 < c / (2 * C) := by positivity
  obtain ⟨x, hx, hlo, hsmall⟩ := (hf.and (hbound.and (h.bound heps))).exists
  simp only [Real.norm_eq_abs, abs_of_pos hx] at hsmall
  have hg : C * g x ≤ C * |g x| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hC.le
  have hh := (hlo.trans hg).trans (mul_le_mul_of_nonneg_left hsmall hC.le)
  have heq : C * (c / (2 * C) * f x) = c * f x / 2 := by field_simp
  rw [heq] at hh
  nlinarith [mul_pos hc hx]

lemma natCast_rpow_isLittleO_of_lt {a b : ℝ} (hab : a < b) :
    (fun d : ℕ => (d : ℝ) ^ a) =o[atTop] (fun d : ℕ => (d : ℝ) ^ b) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact fun h => ((Real.rpow_pos_of_pos hpos b).ne' h).elim
  · have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    change (d : ℝ) ^ (-(b - a)) = (d : ℝ) ^ a / (d : ℝ) ^ b
    rw [neg_sub, Real.rpow_sub hpos]

end AffineCurveCounting
