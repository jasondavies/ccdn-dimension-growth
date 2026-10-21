/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TwoTorsion
import CCDN.ClassGroup.StronglyAmbiguousClassCount

/-!
An internally proved quadratic class-group descent estimate.
The unit obstruction, invariant-ideal decomposition, and finite
discriminant-prime cover are all constructed in the preceding modules.
The resulting discriminant-prime coefficient is sufficient for
subpower absorption; no sharp relative-discriminant genus formula is
asserted.

The degree-one base case for descent on the number-field degree.
The ring of integers is identified with the integers, so its
class group and its two-torsion subgroup are trivial.
-/

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

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

/-- A quadratic extension has two-torsion controlled by base-field
two-torsion and a proved discriminant-prime factor. The constant loss
from units is retained explicitly. -/
theorem quadratic_classGroupTwoTorsion_descent
    (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
    [Algebra F K] (hd : Module.finrank F K = 2) :
    classGroupTwoTorsionCard K ≤
      (classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card +
          Module.finrank ℚ F)) ^ 2 := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have : Nontrivial (K ≃ₐ[F] K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsGalois.card_aut_eq_finrank, hd]; omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : K ≃ₐ[F] K)
  calc
    _ ≤ (Nat.card (stronglyAmbiguousTwoTorsion F K σ) *
        2 ^ Module.finrank ℚ F) ^ 2 :=
      classGroupTwoTorsionCard_le_stronglyAmbiguous F K hd σ hσ
    _ ≤ ((classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card)) *
        2 ^ Module.finrank ℚ F) ^ 2 :=
      Nat.pow_le_pow_left
        (Nat.mul_le_mul_right _
          (stronglyAmbiguousTwoTorsion_card_le_discriminant_primes F K hd σ hσ)) 2
    _ = _ := by rw [mul_assoc, ← pow_add]

/-- The quadratic-degree base case is already subpower in the
discriminant: only the number of its distinct prime divisors occurs. -/
theorem quadratic_field_classGroupTwoTorsionCard_le
    (K : Type*) [Field K] [NumberField K] (hd : Module.finrank ℚ K = 2) :
    classGroupTwoTorsionCard K ≤
      2 ^ (4 * (NumberField.discr K).natAbs.primeFactors.card + 2) := by
  have hh := quadratic_classGroupTwoTorsion_descent ℚ K hd
  rw [classGroupTwoTorsionCard_eq_one_of_degree_one ℚ (by simp),
    hd, Module.finrank_self, one_mul, ← pow_mul] at hh
  convert hh using 1
  congr 1
  ring

end
end CCDN
