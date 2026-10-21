/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.IdealPowerLayer
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! The mod-`p` local layers used in the general local determinant
lemma. A ring homomorphism from a local ring to `ZMod p` is automatically
surjective and has the maximal ideal as kernel. Consequently the residue
field and every Noetherian adic truncation are finite. -/

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

/-- Dimensions of the layers of the maximal ideal of `R/(p)`. -/
def localPrimeLayerDimension [Fact p.Prime] (k : ℕ) : ℕ :=
  Module.finrank (ZMod p) (Ideal.powerLayer (ZMod p) (localPrimeMaximalIdeal R p) k)

variable {R p} [Fact p.Prime]

lemma local_zmod_kernel (ρ : R →+* ZMod p) :
    RingHom.ker ρ = maximalIdeal R :=
  IsLocalRing.ker_eq_maximalIdeal ρ (ZMod.ringHom_surjective ρ)

private def localZModResidueEquiv (ρ : R →+* ZMod p) :
    (R ⧸ maximalIdeal R) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (local_zmod_kernel ρ).symm).trans
    (ρ.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ρ))

private lemma prime_span_le_maximalIdeal (ρ : R →+* ZMod p) :
    Ideal.span {(p : R)} ≤ maximalIdeal R := by
  rw [← local_zmod_kernel ρ]
  apply Ideal.span_le.mpr
  rintro _ rfl
  change ρ (p : R) = 0
  simp

/-- The residue quotient of `R/(p)` is the finite field `F_p`. -/
private def localPrimeReductionResidueEquiv (ρ : R →+* ZMod p) :
    (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) ≃+* ZMod p :=
  (DoubleQuot.quotQuotEquivQuotOfLE (prime_span_le_maximalIdeal ρ)).trans
    (localZModResidueEquiv ρ)

private lemma localPrimeReduction_finite_residue (ρ : R →+* ZMod p) :
    Finite (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) :=
  Finite.of_injective (localPrimeReductionResidueEquiv ρ)
    (localPrimeReductionResidueEquiv ρ).injective

/-- Generators in `R/(p)`, indexed by its layer dimensions. -/
theorem exists_localPrimeReduction_generators [IsNoetherianRing R]
    (ρ : R →+* ZMod p) :
    ∃ g : (k : ℕ) → Fin (localPrimeLayerDimension R p k) → LocalPrimeReduction R p,
      (∀ k j, g k j ∈ localPrimeMaximalIdeal R p ^ k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (localPrimeLayerDimension R p k.val) → ZMod p,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ localPrimeMaximalIdeal R p ^ N := by
  let : Finite (LocalPrimeReduction R p ⧸ localPrimeMaximalIdeal R p) :=
    localPrimeReduction_finite_residue ρ
  exact Ideal.exists_truncation_generators (K := ZMod p)
    (localPrimeMaximalIdeal R p)

end
end CCDN
