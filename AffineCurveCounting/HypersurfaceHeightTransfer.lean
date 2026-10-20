module

public import AffineCurveCounting.WeightedHeightRatio
public import AffineCurveCounting.HypersurfaceBadPrimeFactor
public import AffineCurveCounting.IntegerCoefficientHeight

/-! CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

lemma dimension_root_le_degree {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have he : 1 / (r : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hr1
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 he

/-- The coefficient-weighted ratio has loss at most r in dimension r. -/
theorem hypersurface_logarithmic_height_transfer {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {H Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H) :
    (Real.log H + (d : ℝ) ^ 2) / H ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  apply logarithmic_height_ratio_le hY hYH (by positivity) (by positivity) hr1
  have he : (r : ℝ) * (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))) * (d : ℝ) ^ 2) =
      (d : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) := by field_simp
  rw [he]
  exact (one_le_div hroot).mpr (dimension_root_le_degree hr hd)

/-- CCDN Lemma 4.2.3 with an explicit dimension constant. The coefficient
height is the actual maximum, and the bad-prime factor is the defined factor. -/
theorem hypersurface_badPrime_height_transfer {n d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hd : 0 < d)
    {Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ (integerCoefficientHeight f : ℝ)) :
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤
      ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)) *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) /
          Y ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let H := (integerCoefficientHeight f : ℝ)
  have hH : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let C := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hbad : hypersurfaceBadPrimeFactor f ≤ C * (1 + Real.log H / (d : ℝ) ^ 2) := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio : (Real.log H + (d : ℝ) ^ 2) / H ^ q ≤
      (n + 1 : ℝ) * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hypersurface_logarithmic_height_transfer (r := n + 1) (by omega) hd hY hYH
  have hpowers : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) =
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd0]
    congr 1
    norm_num
    ring
  have hstep : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f / H ^ q ≤
      C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((Real.log H + (d : ℝ) ^ 2) / H ^ q) := by
    calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * (C * (1 + Real.log H / (d : ℝ) ^ 2)) / H ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbad (by positivity)) (by positivity)
      _ = _ := by rw [hpowers]; field_simp; ring
  have hlast := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) by positivity)
  apply hstep.trans
  convert hlast using 1
  dsimp only [C]
  ring

end
end AffineCurveCounting
