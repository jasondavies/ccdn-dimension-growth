module

public import CCDN.IdealAdicLayerQuotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Localization at a maximal ideal preserves every adic layer.
The comparison is induced by the standard isomorphism of finite adic
quotients, and identifies the images of the corresponding ideal powers. -/

@[expose] public section
namespace CCDN
noncomputable section
open IsLocalRing

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (I : Ideal R) [I.IsMaximal] [IsLocalization.AtPrime S I] [IsLocalRing S]

def localizationAdicQuotientEquiv (N : ℕ) :
    (R ⧸ I ^ N) ≃ₐ[K] S ⧸ maximalIdeal S ^ N :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow I S N).restrictScalars K

@[simp]
lemma localizationAdicQuotientEquiv_apply_mk (N : ℕ) (x : R) :
    localizationAdicQuotientEquiv (K := K) (S := S) I N (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R S x) := rfl

lemma localizationAdicQuotientEquiv_layer (k : ℕ) :
    (idealPowerLayer K I k).map
      (localizationAdicQuotientEquiv (K := K) (S := S) I (k + 1)).toLinearMap =
        idealPowerLayer K (maximalIdeal S) k := by
  let e := localizationAdicQuotientEquiv (K := K) (S := S) I (k + 1)
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨algebraMap R S x, ?_, rfl⟩
    change algebraMap R S x ∈ maximalIdeal S ^ k
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I S, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨xbar, hxbar⟩ := e.surjective (Ideal.Quotient.mk _ y)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    have he : Ideal.Quotient.mk (maximalIdeal S ^ (k + 1)) (algebraMap R S x) =
        Ideal.Quotient.mk _ y := hxbar
    have hd : algebraMap R S x - y ∈ maximalIdeal S ^ (k + 1) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, he, sub_self]
    have hx : algebraMap R S x ∈ maximalIdeal S ^ k := by
      have h := (maximalIdeal S ^ k).add_mem
        (Ideal.pow_le_pow_right (Nat.le_succ k) hd) hy
      simpa only [sub_add_cancel] using h
    have hxI : x ∈ I ^ k := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal_pow I S k]
      exact hx
    refine Submodule.mem_map.mpr ⟨Ideal.Quotient.mk _ x, ?_, hxbar⟩
    exact Submodule.mem_map.mpr ⟨x, hxI, rfl⟩

/-- Localization preserves the `I^k/I^(k+1)` layer, represented
by its image in the next quotient. -/
def localizationAdicLayerEquiv (k : ℕ) :
    idealPowerLayer K I k ≃ₗ[K] idealPowerLayer K (maximalIdeal S) k :=
  (Submodule.equivMapOfInjective
    (localizationAdicQuotientEquiv (K := K) (S := S) I (k + 1)).toLinearMap
    (localizationAdicQuotientEquiv (K := K) (S := S) I (k + 1)).injective _).trans
      (LinearEquiv.ofEq _ _ (localizationAdicQuotientEquiv_layer I k))

theorem localizationAdicLayer_finrank (k : ℕ) :
    Module.finrank K (idealPowerLayer K (maximalIdeal S) k) =
      Module.finrank K (idealPowerLayer K I k) :=
  (localizationAdicLayerEquiv (K := K) (S := S) I k).finrank_eq.symm

end
end CCDN
