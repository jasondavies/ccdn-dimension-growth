module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Tactic

/-! The algebraic starting point of the class-group application.
Actual classes killed by two have nonzero integral representatives whose
squares are principal. A principal square determines its ideal uniquely;
thus generators chosen for distinct classes are distinct. The norm assertion
uses the absolute value: a signed field norm need not be positive. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField nonZeroDivisors Real

section Dedekind
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma integralIdeal_pow_injective {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (fun I : Ideal R => I ^ m) := by
  intro I J h
  change I ^ m = J ^ m at h
  apply le_antisymm
  · apply Ideal.le_of_dvd
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hm).mp
    rw [h]
  · apply Ideal.le_of_dvd
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hm).mp
    rw [h]

lemma exists_generator_of_class_square_eq_one (I : (Ideal R)⁰)
    (hI : (ClassGroup.mk0 I) ^ 2 = 1) :
    ∃ β : R, β ≠ 0 ∧ (I : Ideal R) ^ 2 = Ideal.span {β} := by
  have hinv : ClassGroup.mk0 I = (ClassGroup.mk0 I)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_two] using hI
  simpa only [pow_two] using ClassGroup.mk0_eq_mk0_inv_iff.mp hinv

lemma ideal_class_eq_of_square_generators_eq
    (I J : (Ideal R)⁰) {β γ : R}
    (hI : (I : Ideal R) ^ 2 = Ideal.span {β})
    (hJ : (J : Ideal R) ^ 2 = Ideal.span {γ}) (hβγ : β = γ) :
    ClassGroup.mk0 I = ClassGroup.mk0 J := by
  have hpow : (I : Ideal R) ^ 2 = (J : Ideal R) ^ 2 := by rw [hI, hJ, hβγ]
  have hIJ : I = J := Subtype.ext (integralIdeal_pow_injective (by norm_num) hpow)
  rw [hIJ]

end Dedekind

variable (K : Type*) [Field K] [NumberField K]

/-- The subgroup of the actual ideal class group killed by two. -/
def classGroupTwoTorsion : Subgroup (ClassGroup (𝓞 K)) :=
  (powMonoidHom 2).ker

omit [NumberField K] in
@[simp] lemma mem_classGroupTwoTorsion (c : ClassGroup (𝓞 K)) :
    c ∈ classGroupTwoTorsion K ↔ c ^ 2 = 1 := Iff.rfl

/-- The number h₂(K) appearing in CCDN Theorem 6. -/
def classGroupTwoTorsionCard : ℕ := Nat.card (classGroupTwoTorsion K)

lemma classGroupTwoTorsionCard_le_classNumber :
    classGroupTwoTorsionCard K ≤ NumberField.classNumber K := by
  classical
  simpa [classGroupTwoTorsionCard, NumberField.classNumber, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective
      (fun c : classGroupTwoTorsion K => (c : ClassGroup (𝓞 K))) Subtype.val_injective

lemma generator_absolute_norm_of_ideal_square (I : Ideal (𝓞 K)) {β : 𝓞 K}
    (hI : I ^ 2 = Ideal.span {β}) :
    (Algebra.norm ℤ β).natAbs = Ideal.absNorm I ^ 2 := by
  rw [← Ideal.absNorm_span_singleton, ← hI, map_pow]

lemma generator_norm_eq_signed_square (I : Ideal (𝓞 K)) {β : 𝓞 K}
    (hI : I ^ 2 = Ideal.span {β}) :
    Algebra.norm ℤ β = (Ideal.absNorm I : ℤ) ^ 2 ∨
      Algebra.norm ℤ β = -((Ideal.absNorm I : ℤ) ^ 2) := by
  have h := generator_absolute_norm_of_ideal_square K I hI
  have h' : |Algebra.norm ℤ β| = (Ideal.absNorm I : ℤ) ^ 2 := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow] using congrArg (Nat.cast : ℕ → ℤ) h
  exact (abs_eq (by positivity)).mp h'

/-- Every actual two-torsion class has a nonzero integral representative
within the usual Minkowski ideal-norm bound, with a nonzero generator of
its square and the resulting exact absolute norm identity. -/
theorem exists_two_torsion_integral_square_representative
    (c : classGroupTwoTorsion K) :
    ∃ I : (Ideal (𝓞 K))⁰, ∃ β : 𝓞 K,
      ClassGroup.mk0 I = c ∧ β ≠ 0 ∧
      (I : Ideal (𝓞 K)) ^ 2 = Ideal.span {β} ∧
      (Algebra.norm ℤ β).natAbs = Ideal.absNorm (I : Ideal (𝓞 K)) ^ 2 ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            Real.sqrt |NumberField.discr K|) := by
  obtain ⟨I, hIc, hInorm⟩ := NumberField.exists_ideal_in_class_of_norm_le c.val
  have hIsq : (ClassGroup.mk0 I) ^ 2 = 1 := by
    rw [hIc]
    exact c.property
  obtain ⟨β, hβ, hIβ⟩ := exists_generator_of_class_square_eq_one I hIsq
  exact ⟨I, β, hIc, hβ, hIβ, generator_absolute_norm_of_ideal_square K _ hIβ, hInorm⟩

/-- Generators can be chosen injectively on the two-torsion class group.
No archimedean bound is asserted here; that is the separate geometry-of-numbers
step required in the class-group reduction. -/
theorem exists_injective_two_torsion_square_generators :
    ∃ β : classGroupTwoTorsion K → 𝓞 K, Function.Injective β ∧
      ∀ c, β c ≠ 0 ∧ ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = c ∧ (I : Ideal (𝓞 K)) ^ 2 = Ideal.span {β c} ∧
          (Algebra.norm ℤ (β c)).natAbs = Ideal.absNorm (I : Ideal (𝓞 K)) ^ 2 := by
  classical
  choose I β hc hβ hsq hnorm hbound using exists_two_torsion_integral_square_representative K
  refine ⟨β, ?_, fun c => ⟨hβ c, I c, hc c, hsq c, hnorm c⟩⟩
  intro c e hce
  apply Subtype.ext
  rw [← hc c, ← hc e]
  exact ideal_class_eq_of_square_generators_eq (I c) (I e) (hsq c) (hsq e) hce

end
end CCDN
