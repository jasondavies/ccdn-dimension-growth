module

public import CCDN.NoetherianLocalLayers
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The actual mod-`p` local layers used in the general local determinant
lemma. A ring homomorphism from a local ring to `ZMod p` is automatically
surjective and has the maximal ideal as kernel. Consequently the residue
field and every Noetherian adic truncation are finite, without a supplied
residue-field identification or generating family. -/

@[expose] public section
namespace CCDN
noncomputable section
open IsLocalRing

variable (R : Type*) [CommRing R] (p : ℕ)

abbrev LocalPrimeReduction := R ⧸ Ideal.span {(p : R)}

/-- The canonical prime-field algebra on `R/(p)`, including the zero ring. -/
instance localPrimeReduction_zmodAlgebra : Algebra (ZMod p) (LocalPrimeReduction R p) :=
  ZMod.algebra' (LocalPrimeReduction R p) (ringChar (LocalPrimeReduction R p))
    ((CharP.cast_eq_zero_iff (LocalPrimeReduction R p)
      (ringChar (LocalPrimeReduction R p)) p).mp (by
        change Ideal.Quotient.mk (Ideal.span {(p : R)}) (p : R) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))))

variable [IsLocalRing R]

def localPrimeMaximalIdeal : Ideal (LocalPrimeReduction R p) :=
  (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

/-- Dimensions of the actual layers of the maximal ideal of `R/(p)`. -/
def localPrimeLayerDimension [Fact p.Prime] (k : ℕ) : ℕ :=
  Module.finrank (ZMod p) (idealPowerLayer (ZMod p) (localPrimeMaximalIdeal R p) k)

variable {R p} [Fact p.Prime]

lemma local_zmod_kernel (ρ : R →+* ZMod p) :
    RingHom.ker ρ = maximalIdeal R :=
  IsLocalRing.ker_eq_maximalIdeal ρ (ZMod.ringHom_surjective ρ)

def local_zmod_residue_equiv (ρ : R →+* ZMod p) :
    (R ⧸ maximalIdeal R) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (local_zmod_kernel ρ).symm).trans
    (ρ.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ρ))

lemma prime_span_le_maximalIdeal (ρ : R →+* ZMod p) :
    Ideal.span {(p : R)} ≤ maximalIdeal R := by
  rw [← local_zmod_kernel ρ]
  apply Ideal.span_le.mpr
  rintro _ rfl
  change ρ (p : R) = 0
  simp

/-- The residue quotient of `R/(p)` is the genuine finite field `F_p`. -/
def localPrimeReduction_residue_equiv (ρ : R →+* ZMod p) :
    (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) ≃+* ZMod p :=
  (DoubleQuot.quotQuotEquivQuotOfLE (prime_span_le_maximalIdeal ρ)).trans
    (local_zmod_residue_equiv ρ)

lemma localPrimeReduction_finite_residue (ρ : R →+* ZMod p) :
    Finite (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) :=
  Finite.of_injective (localPrimeReduction_residue_equiv ρ)
    (localPrimeReduction_residue_equiv ρ).injective

omit [Fact p.Prime] in
/-- The image of the maximal ideal really is the maximal ideal of the
nonzero quotient. This records the local-ring meaning of the layer profile. -/
lemma localPrimeMaximalIdeal_eq
    [IsLocalRing (LocalPrimeReduction R p)] :
    localPrimeMaximalIdeal R p = maximalIdeal (LocalPrimeReduction R p) :=
  IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (Ideal.span {(p : R)})) Ideal.Quotient.mk_surjective

/-- Actual generators in `R/(p)`, indexed by its actual layer dimensions. -/
theorem exists_localPrimeReduction_generators [IsNoetherianRing R]
    (ρ : R →+* ZMod p) :
    ∃ g : (k : ℕ) → Fin (localPrimeLayerDimension R p k) → LocalPrimeReduction R p,
      (∀ k j, g k j ∈ localPrimeMaximalIdeal R p ^ k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (localPrimeLayerDimension R p k.val) → ZMod p,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ localPrimeMaximalIdeal R p ^ N := by
  let : Finite (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) :=
    localPrimeReduction_finite_residue ρ
  exact exists_noetherian_truncation_generators (K := ZMod p)
    (localPrimeMaximalIdeal R p)

end
end CCDN
