module

public import CCDN.ClassGroupTwoTorsion
public import Mathlib.LinearAlgebra.Dimension.Free

/-! The degree-one base case for descent on the number-field degree.
The ring of integers is identified with the integers, so its actual
class group and its two-torsion subgroup are trivial. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

theorem classGroupTwoTorsionCard_eq_one_of_degree_one
    (K : Type*) [Field K] [NumberField K] (hd : Module.finrank ℚ K = 1) :
    classGroupTwoTorsionCard K = 1 := by
  obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hd
  let eO : ℤ ≃+* 𝓞 K :=
    Rat.ringOfIntegersEquiv.symm.trans (RingOfIntegers.mapRingEquiv e.toRingEquiv)
  have : IsPrincipalIdealRing (𝓞 K) :=
    IsPrincipalIdealRing.of_surjective eO eO.surjective
  apply Nat.le_antisymm
  · exact (classGroupTwoTorsionCard_le_classNumber K).trans
      (NumberField.classNumber_eq_one_iff.mpr inferInstance).le
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.card_pos (α := classGroupTwoTorsion K)).ne'

end
end CCDN
