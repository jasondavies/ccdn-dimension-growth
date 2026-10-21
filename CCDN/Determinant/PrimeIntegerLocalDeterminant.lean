module

public import CCDN.Determinant.NoetherianLocalDeterminant
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Localization.Submodule

/-! The arbitrary Noetherian local determinant lemma with its target
`ℤ_(p)`. Its residue map and prime-generated maximal ideal are constructed
from localization. -/

@[expose] public section
namespace CCDN
noncomputable section
open IsLocalRing

/-- The localization of the integers at the prime ideal `(p)`. -/
abbrev PrimeIntegerLocalization (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime (Ideal.span {(p : ℤ)})

variable (p : ℕ) [Fact p.Prime]

/-- The residue homomorphism `ℤ_(p) → F_p`. -/
def primeIntegerLocalizationResidue :
    PrimeIntegerLocalization p →+* ZMod p :=
  (Int.quotientSpanNatEquivZMod p).toRingHom.comp
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal
      (Ideal.span {(p : ℤ)}) (PrimeIntegerLocalization p)).symm.toRingHom.comp
        (Ideal.Quotient.mk (maximalIdeal (PrimeIntegerLocalization p))))

lemma primeIntegerLocalization_maximalIdeal :
    maximalIdeal (PrimeIntegerLocalization p) =
      Ideal.span {(p : PrimeIntegerLocalization p)} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (Ideal.span {(p : ℤ)}) (PrimeIntegerLocalization p)]
  rw [Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]

lemma primeIntegerLocalizationResidue_kernel :
    RingHom.ker (primeIntegerLocalizationResidue p) =
      Ideal.span {(p : PrimeIntegerLocalization p)} := by
  rw [← primeIntegerLocalization_maximalIdeal p]
  ext x
  change primeIntegerLocalizationResidue p x = 0 ↔
    x ∈ maximalIdeal (PrimeIntegerLocalization p)
  simp only [primeIntegerLocalizationResidue, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 2.4, with the exact sum of the first `s` local-layer weights.
The source need not carry a `ℤ_(p)`-algebra structure: the proof uses only
the given evaluation homomorphisms. -/
theorem primeInteger_local_initial_weight_det {s : ℕ}
    (ψ : Fin s → R →+* PrimeIntegerLocalization p) (x : Fin s → R)
    (w : Fin s → ℕ)
    (hw : IsInitialWeightSegment (localPrimeLayerDimension R p) w) :
    (p : PrimeIntegerLocalization p) ^ (∑ i, w i) ∣
      (Matrix.of fun i j => ψ i (x j)).det :=
  noetherian_local_initial_weight_det (primeIntegerLocalizationResidue p)
    (primeIntegerLocalizationResidue_kernel p) ψ x w hw

/-- The paper's nondecreasing enumeration of the layer
multiplicities gives the same exact determinant exponent. -/
theorem primeInteger_local_enumerated_weight_det {s : ℕ}
    (ψ : Fin s → R →+* PrimeIntegerLocalization p) (x : Fin s → R)
    (a : ℕ → ℕ) (ha : Monotone a)
    (hfinite : ∀ k, {i | a i = k}.Finite)
    (hcount : ∀ k, {i | a i = k}.ncard = localPrimeLayerDimension R p k) :
    (p : PrimeIntegerLocalization p) ^ (∑ i : Fin s, a i.val) ∣
      (Matrix.of fun i j => ψ i (x j)).det :=
  primeInteger_local_initial_weight_det p ψ x _
    (monotone_enumeration_isInitialWeightSegment a
      (localPrimeLayerDimension R p) ha hfinite hcount s)

/-- Finite profiles are allowed whenever they contain at least `s` weights. -/
theorem primeInteger_local_exists_initial_weight_det {s : ℕ}
    (ψ : Fin s → R →+* PrimeIntegerLocalization p) (x : Fin s → R)
    (hcapacity : ∃ N, s ≤ weightProfileCumulative (localPrimeLayerDimension R p) N) :
    ∃ w : Fin s → ℕ, Monotone w ∧
      IsInitialWeightSegment (localPrimeLayerDimension R p) w ∧
      (p : PrimeIntegerLocalization p) ^ (∑ i, w i) ∣
        (Matrix.of fun i j => ψ i (x j)).det := by
  obtain ⟨w, hmono, hw⟩ :=
    exists_initial_weight_segment (localPrimeLayerDimension R p) s hcapacity
  exact ⟨w, hmono, hw, primeInteger_local_initial_weight_det p ψ x w hw⟩

/-- If the profile has fewer than `s` weights in total, every
determinant is zero. This also covers Artinian mod-prime reductions. -/
theorem primeInteger_local_det_eq_zero_of_insufficient_layers {s : ℕ}
    (ψ : Fin s → R →+* PrimeIntegerLocalization p) (x : Fin s → R)
    (hcapacity : ¬ ∃ N, s ≤ weightProfileCumulative (localPrimeLayerDimension R p) N) :
    (Matrix.of fun i j => ψ i (x j)).det = 0 := by
  classical
  let I := maximalIdeal (PrimeIntegerLocalization p)
  have hdiv (e : ℕ) : (p : PrimeIntegerLocalization p) ^ e ∣
      (Matrix.of fun i j => ψ i (x j)).det := by
    apply noetherian_local_det_of_weight_threshold (primeIntegerLocalizationResidue p)
      (primeIntegerLocalizationResidue_kernel p) ψ x
    intro t
    have hcard := Fintype.card_le_of_injective t t.injective
    simp only [Fintype.card_fin, Fintype.card_sigma] at hcard
    have hle : (∑ k : Fin e, localPrimeLayerDimension R p k.val) ≤
        weightProfileCumulative (localPrimeLayerDimension R p) e := by
      rw [weightProfileCumulative, ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_right _ _
    exact False.elim (hcapacity ⟨e, hcard.trans hle⟩)
  have hmem : (Matrix.of fun i j => ψ i (x j)).det ∈ ⨅ e : ℕ, I ^ e := by
    apply Ideal.mem_iInf.mpr
    intro e
    dsimp only [I]
    rw [primeIntegerLocalization_maximalIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (hdiv e)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I (maximalIdeal.isMaximal _).ne_top] at hmem
  exact hmem

/-- Finite-profile formulation: either the exact first `s`
weights exist and give the divisor, or the determinant vanishes. -/
theorem primeInteger_local_det_profile_dichotomy {s : ℕ}
    (ψ : Fin s → R →+* PrimeIntegerLocalization p) (x : Fin s → R) :
    (∃ w : Fin s → ℕ, Monotone w ∧
      IsInitialWeightSegment (localPrimeLayerDimension R p) w ∧
      (p : PrimeIntegerLocalization p) ^ (∑ i, w i) ∣
        (Matrix.of fun i j => ψ i (x j)).det) ∨
      (Matrix.of fun i j => ψ i (x j)).det = 0 := by
  by_cases h : ∃ N, s ≤ weightProfileCumulative (localPrimeLayerDimension R p) N
  · exact Or.inl (primeInteger_local_exists_initial_weight_det p ψ x h)
  · exact Or.inr (primeInteger_local_det_eq_zero_of_insufficient_layers p ψ x h)

end
end CCDN
