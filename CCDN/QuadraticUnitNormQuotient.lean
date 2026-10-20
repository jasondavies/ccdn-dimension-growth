module

public import CCDN.NumberFieldUnitSquareClasses
public import Mathlib.NumberTheory.NumberField.Norm

/-! The unit-norm quotient in a quadratic extension is finite,
with a uniform bound depending only on the base-field degree. Squares
of base units are norms of their extensions. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

def relativeUnitNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ :=
  Units.map (RingOfIntegers.norm F)

theorem relativeUnitNorm_extended (u : (𝓞 F)ˣ) :
    relativeUnitNorm F K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u) =
      u ^ Module.finrank F K := by
  apply Units.ext
  exact RingOfIntegers.norm_algebraMap F u

abbrev quadraticUnitNormQuotient :=
  (𝓞 F)ˣ ⧸ (relativeUnitNorm F K).range

theorem quadraticUnitNormQuotient_square (hd : Module.finrank F K = 2)
    (x : quadraticUnitNormQuotient F K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u, ?_⟩
    rw [relativeUnitNorm_extended, hd]

variable [NumberField F]

theorem quadraticUnitNormQuotient_finite (hd : Module.finrank F K = 2) :
    Finite (quadraticUnitNormQuotient F K) :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).1

/-- Uniform bound on the unit-norm obstruction. -/
theorem quadraticUnitNormQuotient_card_le (hd : Module.finrank F K = 2) :
    Nat.card (quadraticUnitNormQuotient F K) ≤
      2 ^ (NumberField.Units.rank F + 1) :=
  (numberFieldUnit_exponent_two_quotient F
    (QuotientGroup.mk' (relativeUnitNorm F K).range)
    (QuotientGroup.mk'_surjective _) (quadraticUnitNormQuotient_square F K hd)).2

theorem quadraticUnitNormQuotient_card_le_degree (hd : Module.finrank F K = 2) :
    Nat.card (quadraticUnitNormQuotient F K) ≤ 2 ^ Module.finrank ℚ F :=
  (quadraticUnitNormQuotient_card_le F K hd).trans
    (Nat.pow_le_pow_right (by norm_num) (numberField_unit_rank_add_one_le_degree F))

end
end CCDN
