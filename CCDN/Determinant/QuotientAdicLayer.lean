/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.NoetherianLocalLayers

/-! Adic layers in a quotient ring are identified with the corresponding
images in the single quotient by the sum of the equation ideal and the
next ideal power. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

def quotientAdicQuotientEquiv (J I : Ideal A) (N : ℕ) :
    ((A ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) ^ N) ≃ₐ[K] A ⧸ J ⊔ I ^ N :=
  (Ideal.quotientEquivAlgOfEq K (Ideal.map_pow (Ideal.Quotient.mk J) I N).symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ K J (I ^ N))

lemma quotientAdicQuotientEquiv_layer (J I : Ideal A) (k : ℕ) :
    (idealPowerLayer K (I.map (Ideal.Quotient.mk J)) k).map
      (quotientAdicQuotientEquiv (K := K) J I (k + 1)).toLinearMap =
      ((I ^ k).restrictScalars K).map
        (Ideal.Quotient.mkₐ K (J ⊔ I ^ (k + 1))).toLinearMap := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨xbar, hxbar, rfl⟩ := Submodule.mem_map.mp hy
    change xbar ∈ (I.map (Ideal.Quotient.mk J)) ^ k at hxbar
    rw [← Ideal.map_pow] at hxbar
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hxbar
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    refine Submodule.mem_map.mpr
      ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk J x), ?_, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J x, ?_, rfl⟩
    change Ideal.Quotient.mk J x ∈ (I.map (Ideal.Quotient.mk J)) ^ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx

def quotientAdicLayerEquiv (J I : Ideal A) (k : ℕ) :
    idealPowerLayer K (I.map (Ideal.Quotient.mk J)) k ≃ₗ[K]
      ((I ^ k).restrictScalars K).map
        (Ideal.Quotient.mkₐ K (J ⊔ I ^ (k + 1))).toLinearMap :=
  (Submodule.equivMapOfInjective
    (quotientAdicQuotientEquiv (K := K) J I (k + 1)).toLinearMap
    (quotientAdicQuotientEquiv (K := K) J I (k + 1)).injective _).trans
      (LinearEquiv.ofEq _ _ (quotientAdicQuotientEquiv_layer J I k))

end
end CCDN
