module

public import CCDN.QuadraticInvariantFactorization
public import CCDN.InvariantIdealIntegralRepresentative
public import CCDN.QuadraticAmbiguousClassBound
public import CCDN.FiniteGroupTorsionCover
public import CCDN.IntegralIdealClass
public import CCDN.DiscriminantPrimeIdealCover

/-! The two-torsion in the actual strongly ambiguous class group is
bounded by base-field two-torsion and the finite set of ramified primes.
The cover comes from the proved invariant-ideal factorization. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped Classical Pointwise nonZeroDivisors

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

theorem stronglyAmbiguousClassGroup_ramified_cover
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q, IsQuadraticRamifiedPrime F K Q → Q ∈ S)
    (c : stronglyAmbiguousClassGroup F K σ) :
    ∃ a : ClassGroup (𝓞 F), ∃ t : S.powerset,
      c.val = ClassGroup.extendedHom (𝓞 F) (𝓞 K) a *
        ∏ Q ∈ t.val, integralIdealClass Q := by
  obtain ⟨J, hJ, hJc⟩ := (mem_stronglyAmbiguousClassGroup F K σ c.val).mp c.property
  have hσO : Function.Involutive (RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
    intro x
    apply RingOfIntegers.ext
    exact quadratic_automorphism_involutive F K hd σ (x : K)
  obtain ⟨I, hIinv, hIc⟩ :=
    exists_invariant_integral_ideal_representative
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv hσO J hJ
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hIinv' : σ • (I : Ideal (𝓞 K)) = I := by
    rw [quadratic_integer_ideal_action]
    exact hIinv
  have hc : integralIdealClass (I : Ideal (𝓞 K)) = c.val :=
    (integralIdealClass_mk0 I).trans (hIc.trans hJc)
  obtain ⟨A, t, hA, ht, hfact⟩ :=
    invariant_integral_ideal_ramified_factorization F K hd σ hσ I hI0 hIinv'
  have htS : t ⊆ S := fun Q hQ ↦ hS Q (ht Q hQ)
  have ht0 : ∀ Q ∈ t, Q ≠ 0 := fun Q hQ ↦ (ht Q hQ).2.1
  have hmap0 : A.map (algebraMap (𝓞 F) (𝓞 K)) ≠ 0 :=
    Ideal.map_ne_bot_of_ne_bot hA
  refine ⟨integralIdealClass A, ⟨t, Finset.mem_powerset.mpr htS⟩, ?_⟩
  rw [← hc, hfact, integralIdealClass_mul hmap0 (Finset.prod_ne_zero_iff.mpr ht0),
    integralIdealClass_extension (𝓞 K) A hA, integralIdealClass_prod t ht0]

theorem stronglyAmbiguousTwoTorsion_card_le_ramified_cover
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q, IsQuadraticRamifiedPrime F K Q → Q ∈ S) :
    Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F * 2 ^ S.card := by
  have hh := power_torsion_card_le_of_coset_cover
    (ClassGroup.extendedHom (𝓞 F) (𝓞 K)) (stronglyAmbiguousClassGroup F K σ)
    (fun t : S.powerset ↦ ∏ Q ∈ t.val, integralIdealClass Q)
    (stronglyAmbiguousClassGroup_ramified_cover F K hd σ hσ S hS) 2
  simpa only [Fintype.card_coe, Finset.card_powerset, stronglyAmbiguousTwoTorsion,
    classGroupTwoTorsionCard, classGroupTwoTorsion] using hh

/-- A fully constructed discriminant-prime cover gives the actual
strongly ambiguous two-torsion estimate. -/
theorem stronglyAmbiguousTwoTorsion_card_le_discriminant_primes
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card) := by
  have hh := stronglyAmbiguousTwoTorsion_card_le_ramified_cover F K hd σ hσ
    (discriminantPrimeIdealCover K) (by
      intro Q hQ
      have : Q.IsPrime := hQ.1
      exact mem_discriminantPrimeIdealCover_of_ramification_two K F Q hQ.2.1 hQ.2.2)
  exact hh.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (discriminantPrimeIdealCover_card_le K)))

end
end CCDN
