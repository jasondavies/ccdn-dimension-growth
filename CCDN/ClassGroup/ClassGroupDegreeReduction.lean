/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NoIndexTwoClassGroupBound
public import CCDN.ClassGroup.QuadraticClassGroupDescent
/-! Degree and discriminant facts used to assemble the class-group bound
by strong induction on the number-field degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

variable (K : Type*) [Field K] [NumberField K]

lemma one_le_log_discr_natAbs_add_one : 1 ≤ Real.log ((discr K).natAbs : ℝ) + 1 := by
  rw [numberField_discriminant_natAbs_cast]
  linarith [Real.log_nonneg (one_le_abs_discr K)]

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
