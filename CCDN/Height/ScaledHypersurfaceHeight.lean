/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Algebra.ScaledHomogenization
import CCDN.ForMathlib.MvPolynomial
/-! The exact leading homogeneous coefficient height supplies the full
scaling gain in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The highest homogeneous part gains precisely h^d in coefficient height. -/
theorem scaledHomogenize_leading_height_lower {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {h : ℤ} (hh : 1 ≤ h) :
    (h : ℝ) ^ f.totalDegree *
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpow : (0 : ℝ) < (h : ℝ) ^ f.totalDegree := by positivity
  have hc : (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) / (h : ℝ) ^ f.totalDegree := by
    apply integerCoefficientHeight_le _ (by positivity)
    intro m
    rw [coeff_homogeneousComponent]
    split_ifs with hm
    · have hm' : m.sum (fun _ e => e) = f.totalDegree := hm
      have he := coefficient_abs_le_integerCoefficientHeight (scaledHomogenize f.totalDegree h f)
        (homogenizedExponent f.totalDegree m)
      rw [scaledHomogenize_coefficient, hm', Int.cast_mul, Int.cast_pow, abs_mul,
        abs_pow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)] at he
      exact (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using he)
    · simp only [Int.cast_zero, abs_zero]
      positivity
  have he := (le_div_iff₀ hpow).mp hc
  simpa only [mul_comm] using he

lemma leading_height_one_le {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    (1 : ℝ) ≤ integerCoefficientHeight (homogeneousComponent f.totalDegree f) := by
  exact_mod_cast integerCoefficientHeight_pos _ (homogeneousComponent_totalDegree_ne_zero hf)

end
end CCDN
