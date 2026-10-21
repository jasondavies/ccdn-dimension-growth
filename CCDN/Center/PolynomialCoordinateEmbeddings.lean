/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! Original affine coordinates separate embeddings of the function field
of a parameter-polynomial coordinate ring when the coefficient field
already contains every polynomial parameter. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K R F L σ τ : Type*} [Field K] [Field R] [Field F] [Field L]
  [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
  [Algebra K L] [Algebra R L] [IsScalarTower K R L]
  (I : Ideal (MvPolynomial σ K))
  [Algebra (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]
  [IsScalarTower K (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]
  [IsFractionRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F]

private theorem polynomial_coordinate_embeddings_injective
    (hparam : ∀ j : τ, ∃ r : R, algebraMap R F r =
      algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F (X j)) :
    Function.Injective (fun φ : F →ₐ[R] L => fun j : σ =>
      φ (algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F
        (C (Ideal.Quotient.mk I (X j))))) := by
  intro φ ψ he
  let A := MvPolynomial σ K ⧸ I
  let T := MvPolynomial τ A
  let η : T →ₐ[K] F := IsScalarTower.toAlgHom K T F
  let q : MvPolynomial σ K →ₐ[K] F := η.comp
    ((IsScalarTower.toAlgHom K A T).comp (Ideal.Quotient.mkₐ K I))
  have hpoly : (φ.restrictScalars K).comp q = (ψ.restrictScalars K).comp q := by
    apply MvPolynomial.algHom_ext
    intro j
    exact congrFun he j
  have hT : φ.toRingHom.comp (algebraMap T F) = ψ.toRingHom.comp (algebraMap T F) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
      exact AlgHom.congr_fun hpoly f
    · intro j
      obtain ⟨r,hr⟩ := hparam j
      change φ (algebraMap T F (X j)) = ψ (algebraMap T F (X j))
      rw [← hr,φ.commutes,ψ.commutes]
  have hfield : φ.toRingHom = ψ.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := T)
    intro a
    exact RingHom.congr_fun hT a
  ext x
  exact RingHom.congr_fun hfield x

theorem neg_polynomial_coordinate_embeddings_injective
    (hparam : ∀ j : τ, ∃ r : R, algebraMap R F r =
      algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F (X j)) :
    Function.Injective (fun φ : F →ₐ[R] L => fun j : σ =>
      φ (-algebraMap (MvPolynomial τ (MvPolynomial σ K ⧸ I)) F
        (C (Ideal.Quotient.mk I (X j))))) := by
  intro φ ψ he
  apply polynomial_coordinate_embeddings_injective I hparam
  funext j
  exact neg_injective (by simpa only [map_neg] using congrFun he j)

end
end CCDN
