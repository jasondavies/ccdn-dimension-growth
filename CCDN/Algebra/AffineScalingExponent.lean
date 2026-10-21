module

public import CCDN.Height.HypersurfaceHeightTransfer
/-! The prime-scaled height gain gives the affine exponent 1/d^(1/r). -/

@[expose] public section
namespace CCDN

lemma affine_scaling_box_power {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {B A p : ℝ} (hB : 1 ≤ B) (hA : 1 ≤ A) (hp : 0 < p) (hBp : B / A ≤ p) :
    B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) /
        p ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      A * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) := Real.one_le_rpow hd1 (by positivity)
  have hr0 : (0 : ℝ) < r := by linarith
  have hroot0 : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  let β := 1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))).mpr
    exact one_le_mul_of_one_le_of_one_le hr1 hroot
  have hBA : B / p ≤ A := by
    apply (div_le_iff₀ hp).mpr
    have hh := (div_le_iff₀ (by linarith : 0 < A)).mp hBp
    nlinarith
  have hpow : (B / p) ^ β ≤ A :=
    (Real.rpow_le_rpow (by positivity) hBA hβ).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hβ1)
  have he : ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) =
      1 / (d : ℝ) ^ (1 / (r : ℝ)) + β := by dsimp [β]; field_simp
  calc
    _ = B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) * (B / p) ^ β := by
      rw [he, Real.rpow_add (by linarith), Real.div_rpow (by linarith) hp.le]
      ring
    _ ≤ B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) * A :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_comm _ _

lemma scaled_height_rpow {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    (p ^ d * L) ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) =
      p ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) *
        L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  congr 2
  field_simp

end CCDN
