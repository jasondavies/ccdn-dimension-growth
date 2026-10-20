module

public import CCDN.NoetherianLocalLayers
public import Mathlib.LinearAlgebra.Isomorphisms

/-! Identify the layer used in the local determinant proof with the literal
quotient `I^k/I^(k+1)`. The quotient denominator is restricted to `I^k`;
the canonical map to `A/I^(k+1)` has precisely this kernel. -/

@[expose] public section
namespace CCDN
noncomputable section

variable (K : Type*) [Field K] {A : Type*} [CommRing A] [Algebra K A]

def idealPowerLayerDenominator (I : Ideal A) (k : ℕ) :
    Submodule K ((I ^ k).restrictScalars K) :=
  ((I ^ (k + 1)).restrictScalars K).comap ((I ^ k).restrictScalars K).subtype

/-- The standard first-isomorphism identification
`I^k/I^(k+1) ≃ image(I^k → A/I^(k+1))`. -/
def idealPowerLayerQuotientEquiv (I : Ideal A) (k : ℕ) :
    (((I ^ k).restrictScalars K) ⧸ idealPowerLayerDenominator K I k) ≃ₗ[K]
      idealPowerLayer K I k := by
  let φ : ((I ^ k).restrictScalars K) →ₗ[K] A ⧸ I ^ (k + 1) :=
    (Ideal.Quotient.mkₐ K (I ^ (k + 1))).toLinearMap.comp
      ((I ^ k).restrictScalars K).subtype
  have hker : idealPowerLayerDenominator K I k = LinearMap.ker φ := by
    ext x
    change (x : A) ∈ I ^ (k + 1) ↔
      Ideal.Quotient.mk (I ^ (k + 1)) (x : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  have hrange : LinearMap.range φ = idealPowerLayer K I k := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Submodule.mem_map.mpr ⟨y.val, y.property, rfl⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
      exact ⟨⟨y, hy⟩, hxy⟩
  exact (Submodule.quotEquivOfEq _ _ hker).trans
    (φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

lemma idealPowerLayerQuotient_finrank (I : Ideal A) (k : ℕ) :
    Module.finrank K
      (((I ^ k).restrictScalars K) ⧸ idealPowerLayerDenominator K I k) =
      Module.finrank K (idealPowerLayer K I k) :=
  (idealPowerLayerQuotientEquiv K I k).finrank_eq

end
end CCDN
