module

public import CCDN.ProjectivePlaneCoefficientCount

/-! The second inequality of CCDN Corollary 3.1.2 bounds the
coefficient-sensitive expression, so it composes with its first inequality. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The bad-prime factor divided by the coefficient-height saving
is bounded independently of the coefficients and degree. -/
theorem hypersurface_badPrime_div_height_bound {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) :
    hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) ≤
      2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1) := by
  let H := (integerCoefficientHeight f : ℝ)
  let x := Real.log H / (d : ℝ) ^ 2
  let K := 2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 1)
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact_mod_cast integerCoefficientHeight_pos f hf
  have hH0 : 0 < H := by linarith
  have hx : 0 ≤ x := div_nonneg (Real.log_nonneg hH) (sq_nonneg _)
  have hK : 0 ≤ K := mul_nonneg (by positivity)
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hmax : max x 1 ≤ Real.exp x := by
    apply max_le
    · have hh := Real.add_one_le_exp x
      linarith
    · exact Real.one_le_exp hx
  have hpow : H ^ (1 / (d : ℝ) ^ 2) = Real.exp x := by
    rw [Real.rpow_def_of_pos hH0]
    congr 1
    dsimp only [x]
    ring
  have hbad : hypersurfaceBadPrimeFactor f ≤ K * max x 1 := by
    simpa only [hdegree] using
      hypersurfaceBadPrimeFactor_le_max f H hH (coefficient_abs_le_integerCoefficientHeight f)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hH0 _)).mpr
  rw [hpow]
  exact hbad.trans (mul_le_mul_of_nonneg_left hmax hK)

def projectivePlaneCoefficientUniformConstant : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant 0 *
    (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3 + 2)

lemma projectivePlaneCoefficientUniformConstant_pos :
    0 < projectivePlaneCoefficientUniformConstant := by
  unfold projectivePlaneCoefficientUniformConstant
  have hC := hypersurfaceAbsoluteAuxiliaryConstant_pos 0
  have hH := hypersurfaceHeightConstant_one_le 3
  positivity

/-- The literal second bound in CCDN Corollary 3.1.2, with an absolute
constant and the bad-prime factor and maximum coefficient height. -/
theorem projective_plane_coefficient_expression_le {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    hypersurfaceAbsoluteAuxiliaryConstant 0 *
        ((d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * B ^ (2 / (d : ℝ)) /
            (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) +
          d * Real.log B + (d : ℝ) ^ 4) ≤
      projectivePlaneCoefficientUniformConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  let K := 2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3
  let Q := B ^ (2 / (d : ℝ))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hQ0 : 0 ≤ Q := by linarith
  have hratio := hypersurface_badPrime_div_height_bound f hf0 (hf.totalDegree hf0)
  have hfirst : (d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * Q /
      (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) ≤ K * (d : ℝ) ^ 4 * Q := by
    convert mul_le_mul_of_nonneg_left hratio (show 0 ≤ (d : ℝ) ^ 4 * Q by positivity)
      using 1 <;> ring
  have hlog : Real.log B ≤ (d : ℝ) / 2 * Q := by
    have hh := Real.log_le_rpow_div hB0.le (show (0 : ℝ) < 2 / d by positivity)
    convert hh using 1
    dsimp only [Q]
    field_simp
  have hd24 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by
    have hh : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd1
    nlinarith
  have hsecond : (d : ℝ) * Real.log B ≤ (d : ℝ) ^ 4 * Q := by
    have h1 := mul_le_mul_of_nonneg_left hlog hd0.le
    have h2 := mul_le_mul_of_nonneg_right hd24 hQ0
    have h3 : 0 ≤ (d : ℝ) ^ 4 * Q := by positivity
    nlinarith only [h1, h2, h3]
  have hthird : (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 4 * Q :=
    le_mul_of_one_le_right (by positivity) hQ
  have hsum : (d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * Q /
        (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) +
          d * Real.log B + (d : ℝ) ^ 4 ≤ (K + 2) * (d : ℝ) ^ 4 * Q := by
    nlinarith only [hfirst, hsecond, hthird]
  have hh := mul_le_mul_of_nonneg_left hsum (hypersurfaceAbsoluteAuxiliaryConstant_pos 0).le
  convert hh using 1
  unfold projectivePlaneCoefficientUniformConstant
  dsimp only [K, Q]
  ring

/-- Both inequalities in the displayed Corollary 3.1.2 chain hold for
the same primitive irreducible homogeneous equation. -/
theorem projective_plane_coefficient_count_chain {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        hypersurfaceAbsoluteAuxiliaryConstant 0 *
          ((d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * B ^ (2 / (d : ℝ)) /
              (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) +
            d * Real.log B + (d : ℝ) ^ 4) ∧
      hypersurfaceAbsoluteAuxiliaryConstant 0 *
          ((d : ℝ) ^ 4 * hypersurfaceBadPrimeFactor f * B ^ (2 / (d : ℝ)) /
              (integerCoefficientHeight f : ℝ) ^ (1 / (d : ℝ) ^ 2) +
            d * Real.log B + (d : ℝ) ^ 4) ≤
        projectivePlaneCoefficientUniformConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) :=
  ⟨projective_plane_coefficient_count f hf hd hprim hir hB,
    projective_plane_coefficient_expression_le f hf hir.ne_zero hd hB⟩

end
end CCDN
