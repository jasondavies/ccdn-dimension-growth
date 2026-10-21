/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularTangent
public import CCDN.ForMathlib.IdealPowerLayer
import Mathlib.RingTheory.LocalRing.Defs

/-!
The coordinate ring of a hypersurface and its origin ideal. The
origin-adic layers of the coordinate ring are the polynomial
truncation layers.

Adic layers in a quotient ring are identified with the corresponding
images in the single quotient by the sum of the equation ideal and the
next ideal power.
-/

@[expose] public section
namespace CCDN
noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

def quotientAdicQuotientEquiv (J I : Ideal A) (N : ℕ) :
    ((A ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) ^ N) ≃ₐ[K] A ⧸ J ⊔ I ^ N :=
  (Ideal.quotientEquivAlgOfEq K (Ideal.map_pow (Ideal.Quotient.mk J) I N).symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ K J (I ^ N))

lemma quotientAdicQuotientEquiv_layer (J I : Ideal A) (k : ℕ) :
    (Ideal.powerLayer K (I.map (Ideal.Quotient.mk J)) k).map
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
    Ideal.powerLayer K (I.map (Ideal.Quotient.mk J)) k ≃ₗ[K]
      ((I ^ k).restrictScalars K).map
        (Ideal.Quotient.mkₐ K (J ⊔ I ^ (k + 1))).toLinearMap :=
  (Submodule.equivMapOfInjective
    (quotientAdicQuotientEquiv (K := K) J I (k + 1)).toLinearMap
    (quotientAdicQuotientEquiv (K := K) J I (k + 1)).injective _).trans
      (LinearEquiv.ofEq _ _ (quotientAdicQuotientEquiv_layer J I k))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial IsLocalRing

variable {K σ : Type*} [Field K]

lemma idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ K = RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  ext f
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  change (∀ e, Finsupp.degree e < 1 → f.coeff e = 0) ↔ f.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h e he
    have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
    simpa only [he0] using h

lemma idealOfVars_isMaximal : (idealOfVars σ K).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)

abbrev HypersurfaceCoordinateRing (f : MvPolynomial σ K) :=
  MvPolynomial σ K ⧸ Ideal.span {f}

def hypersurfaceOriginIdeal (f : MvPolynomial σ K) :
    Ideal (HypersurfaceCoordinateRing f) :=
  (idealOfVars σ K).map (Ideal.Quotient.mk (Ideal.span {f}))

/-- The affine coordinate ring's origin-adic layer is the polynomial
truncation layer used to compute its Hilbert function. -/
def hypersurfaceCoordinateLayerEquiv (f : MvPolynomial σ K) (k : ℕ) :
    Ideal.powerLayer K (hypersurfaceOriginIdeal f) k ≃ₗ[K] originLayer f k :=
  quotientAdicLayerEquiv (Ideal.span {f}) (idealOfVars σ K) k

end
end CCDN
