module

public import CCDN.ProjectivePlanePositionedCount
public import CCDN.RationalPlaneAssembly

/-! An absolute d^4 B^(2/d) bound for primitive absolutely irreducible
homogeneous plane equations of degree at least two. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def projectivePlaneAbsoluteConstant : ℝ :=
  5 + 2 * Real.exp (heightDeterminantError 164 + 23) * Real.exp 14 * Real.exp 2 +
    (34 + 8 * Real.exp (heightDeterminantError 164 + 20))

lemma projectivePlaneAbsoluteConstant_pos : 0 < projectivePlaneAbsoluteConstant := by
  unfold projectivePlaneAbsoluteConstant
  positivity

lemma projective_positioned_bound_le {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    max ((d : ℝ) * scaledPlaneAuxiliaryDegreeBound d 164 (((d : ℝ) + 1) * B) 1)
      ((34 + 8 * Real.exp (heightDeterminantError 164 + 20)) * (d : ℝ) ^ 4) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by positivity
  have hB0 : 0 < B := by linarith
  let Q := B ^ (2 / (d : ℝ))
  let E := 2 * Real.exp (heightDeterminantError 164 + 23) * Real.exp 14
  let A := 34 + 8 * Real.exp (heightDeterminantError 164 + 20)
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlogplus : Real.log ((d : ℝ) + 1) ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < d + 1 by positivity)
    linarith
  have hlogR : Real.log (((d : ℝ) + 1) * B) ≤ d + Real.log B := by
    rw [Real.log_mul (by positivity) hB0.ne']
    linarith
  have hlogB : Real.log B ≤ (d : ℝ) / 2 * Q := by
    have h := Real.log_le_rpow_div hB0.le (show (0 : ℝ) < 2 / d by positivity)
    convert h using 1
    dsimp only [Q]
    field_simp
  have hpower : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) ≤ Real.exp 2 * Q := by
    rw [Real.mul_rpow (by positivity) hB0.le]
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    linarith
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hdQ : (d : ℝ) ≤ d * Q := by nlinarith
  have hd3Q : (d : ℝ) * Q ≤ (d : ℝ) ^ 3 * Q :=
    mul_le_mul_of_nonneg_right hd3 (by positivity)
  have hrest : (d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2 ≤
      5 * (d : ℝ) ^ 3 * Q := by nlinarith
  have hterm := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ E * (d : ℝ) ^ 3 by positivity)
  have hdeg : scaledPlaneAuxiliaryDegreeBound d 164 (((d : ℝ) + 1) * B) 1 ≤
      (5 + E * Real.exp 2) * (d : ℝ) ^ 3 * Q := by
    unfold scaledPlaneAuxiliaryDegreeBound
    simp only [Real.log_one, zero_div, add_zero, mul_one, Real.one_rpow, div_one]
    dsimp only [E] at hterm ⊢
    nlinarith only [hrest, hterm]
  have hsmall := mul_le_mul_of_nonneg_left hdeg hd0.le
  have hlarge := mul_le_mul_of_nonneg_left hQ (show 0 ≤ A * (d : ℝ) ^ 4 by positivity)
  apply max_le
  · dsimp only [projectivePlaneAbsoluteConstant]
    dsimp only [E, Q] at hsmall
    nlinarith only [hsmall, mul_nonneg hA (mul_nonneg (pow_nonneg hd0.le 4)
      (show 0 ≤ Q by positivity))]
  · dsimp only [projectivePlaneAbsoluteConstant]
    dsimp only [A, Q] at hlarge
    have hpositive : 0 ≤ (5 + E * Real.exp 2) * (d : ℝ) ^ 4 * Q := by positivity
    dsimp only [E, Q] at hpositive
    nlinarith only [hlarge, hpositive]

/-- The full real-radius bound for primitive absolutely irreducible plane
equations of degree >= 2, including their points at infinity. -/
theorem projective_plane_primitive_absolute_count
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  apply projective_zero_count_le_of_family_bound f hf
  intro t z hz0 hinj hzprim hz hbox
  exact (projective_plane_finite_count_positioned f hf hd hprim hir z hz0 hinj hzprim hz hB hbox).trans
    (projective_positioned_bound_le (by omega) hB)

/-- No coefficient normalization hypothesis is required for a rational
absolutely irreducible plane equation. The constant is independent of its
coefficients, degree, and real height radius. -/
theorem projective_plane_rational_absolute_count
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by simp [h])
  obtain ⟨g, a, hg, ha, he⟩ := exists_primitive_integer_model f hf0
  have hgh := rational_scalar_model_homogeneous he hf
  have hgi := rational_scalar_model_irreducible_charZero ha he hir
  have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g) = projectiveZeroLocus f := by
    ext x
    exact rational_scalar_model_zero_iff ha he x.rep
  have h := projective_plane_primitive_absolute_count g hgh hd hg hgi hB
  rwa [hzero] at h

end
end CCDN
