/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Center.PolynomialParameterTranslation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad

/-! Independent values at one parameter specialization imply independence
of the generic polynomial values together with all parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem generic_polynomial_independence
    {K A σ ι : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (p : ι → MvPolynomial σ A) (a : σ → K)
    (ha : AlgebraicIndependent K
      (fun i => eval (fun j => algebraMap K A (a j)) (p i))) :
    AlgebraicIndependent K (Sum.elim (fun j => (X j : MvPolynomial σ A)) p) := by
  let φ : MvPolynomial ι K →ₐ[K] MvPolynomial σ A := aeval p
  have he : ((eval (fun j => algebraMap K A (a j))).comp φ.toRingHom) =
      (aeval (fun i => eval (fun j => algebraMap K A (a j)) (p i))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [φ]
    · intro i
      simp [φ]
  have hφ : Function.Injective
      ((eval (fun j => algebraMap K A (a j))).comp φ.toRingHom) := by
    rw [he]
    exact ha
  have hi := multivariate_deformation_injective_at φ a hφ
  have hcomp : (eval₂Hom φ.toRingHom X).comp (sumAlgEquiv K σ ι).toRingHom =
      (aeval (Sum.elim (fun j => (X j : MvPolynomial σ A)) p)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [φ]
    · intro q
      cases q <;> simp [φ]
  change Function.Injective (aeval (Sum.elim (fun j => (X j : MvPolynomial σ A)) p))
  have hh := hi.comp (sumAlgEquiv K σ ι).injective
  change Function.Injective ((eval₂Hom φ.toRingHom X).comp (sumAlgEquiv K σ ι).toRingHom) at hh
  rw [hcomp] at hh
  exact hh

end
end CCDN
