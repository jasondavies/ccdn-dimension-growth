module

public import CCDN.QuotientAdicLayer

/-! Algebra equivalences preserve ideal-adic layers. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]

def idealPowerLayerEquivOfEq {I J : Ideal A} (h : I = J) (k : ℕ) :
    idealPowerLayer K I k ≃ₗ[K] idealPowerLayer K J k := by
  subst J
  exact LinearEquiv.refl _ _

def algEquivAdicQuotient (e : A ≃ₐ[K] B) (I : Ideal A) (N : ℕ) :
    (A ⧸ I ^ N) ≃ₐ[K] B ⧸ (I.map e.toRingHom) ^ N :=
  Ideal.quotientEquivAlg _ _ e (Ideal.map_pow e.toRingHom I N).symm

lemma algEquivAdicQuotient_layer (e : A ≃ₐ[K] B) (I : Ideal A) (k : ℕ) :
    (idealPowerLayer K I k).map (algEquivAdicQuotient e I (k + 1)).toLinearMap =
      idealPowerLayer K (I.map e.toRingHom) k := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨e x, ?_, rfl⟩
    change e x ∈ (I.map e.toRingHom) ^ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    change y ∈ (I.map e.toRingHom) ^ k at hy
    rw [← Ideal.map_pow] at hy
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hy
    refine Submodule.mem_map.mpr ⟨Ideal.Quotient.mk _ x, ?_, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

def algEquivAdicLayerEquiv (e : A ≃ₐ[K] B) (I : Ideal A) (k : ℕ) :
    idealPowerLayer K I k ≃ₗ[K] idealPowerLayer K (I.map e.toRingHom) k :=
  (Submodule.equivMapOfInjective (algEquivAdicQuotient e I (k + 1)).toLinearMap
    (algEquivAdicQuotient e I (k + 1)).injective _).trans
      (LinearEquiv.ofEq _ _ (algEquivAdicQuotient_layer e I k))

end
end CCDN
