module

public import CCDN.NoIndexTwoClassGroupBound
public import CCDN.QuadraticClassGroupDescent

/-! Degree and discriminant facts used to assemble the class-group bound
by strong induction on the number-field degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

lemma numberField_discriminant_natAbs_cast :
    ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (discr K))

lemma numberField_discriminant_natAbs_pos : 0 < (discr K).natAbs :=
  Int.natAbs_pos.mpr (discr_ne_zero K)

lemma numberField_discriminant_log_ge_one (hn : 2 ≤ Module.finrank ℚ K) :
    1 ≤ Real.log ((discr K).natAbs : ℝ) := by
  have hD3 : (3 : ℝ) ≤ ((discr K).natAbs : ℝ) := by
    have hh : (3 : ℤ) ≤ |discr K| := by
      have := abs_discr_gt_two (K := K) (by omega : 1 < Module.finrank ℚ K)
      omega
    rw [numberField_discriminant_natAbs_cast]
    exact_mod_cast hh
  have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hD3)
  simpa only [Real.log_exp] using h

theorem index_two_subfield_degree
    (hn : 3 ≤ Module.finrank ℚ K) (L : IntermediateField ℚ K)
    (hL : Module.finrank L K = 2) :
    Module.finrank ℚ L = Module.finrank ℚ K / 2 ∧
      2 ≤ Module.finrank ℚ L ∧
      Module.finrank ℚ L < Module.finrank ℚ K := by
  have ht := Module.finrank_mul_finrank ℚ L K
  rw [hL] at ht
  omega

theorem no_index_two_classGroup_log_one_bound
    (hn : 2 ≤ Module.finrank ℚ K)
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
    (classGroupTwoTorsionCard K : ℝ) ≤
      noIndexTwoClassGroupConstant (Module.finrank ℚ K) *
        ((discr K).natAbs : ℝ) ^
          (1 / 2 - 1 / (2 * (Module.finrank ℚ K : ℝ))) *
            (Real.log ((discr K).natAbs : ℝ) + 1) := by
  rw [numberField_discriminant_natAbs_cast]
  apply (no_index_two_classGroup_two_torsion_bound K hn hnoTwo).trans
  exact mul_le_mul_of_nonneg_left (by linarith : Real.log |(discr K : ℝ)| ≤
    Real.log |(discr K : ℝ)| + 1) (by
      exact mul_nonneg (noIndexTwoClassGroupConstant_pos _).le
        (Real.rpow_nonneg (abs_nonneg _) _))

end
end CCDN
