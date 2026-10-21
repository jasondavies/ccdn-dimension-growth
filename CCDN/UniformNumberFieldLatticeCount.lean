module

public import CCDN.NumberFieldLatticeBox
public import CCDN.NumberFieldShortBasis

/-! Uniform finite-radius counts for the ring of integers and its
integer-translation classes. The required short basis is constructed,
and every coefficient depends only on the degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem boundedSquareNormTranslationClasses_uniform_count
    (hn : 2 ≤ Module.finrank ℚ K) {B : ℝ} (hB1 : 1 ≤ B)
    (hB : |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) ((Module.finrank ℚ K : ℝ) ^ 3) *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  apply boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB1
    (by positivity)
  exact fun i ↦ (hnorm i).trans (mul_le_mul_of_nonneg_left hB (by positivity))

end
end CCDN
