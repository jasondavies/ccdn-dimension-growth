/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import CCDN.Algebra.OriginShift
import CCDN.Center.MultivariateDeformation
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
Independent values at one parameter specialization imply independence
of the generic polynomial values together with all parameters.

Specialization at an arbitrary parameter point detects injectivity of
a simultaneous polynomial deformation.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem multivariate_deformation_injective_at
    {K R S σ : Type*} [CommRing K] [CommRing R] [CommRing S] [IsDomain S]
    [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] MvPolynomial σ S) (a : σ → K)
    (hφ : Function.Injective ((eval (fun i => algebraMap K S (a i))).comp φ.toRingHom)) :
    Function.Injective (eval₂Hom φ.toRingHom X) := by
  let tS := originShift (fun i => algebraMap K S (a i))
  let tR := originShift (fun i => algebraMap K R (a i))
  let φ' := tS.comp φ.toRingHom
  have hφ' : Function.Injective ((eval (fun _ => (0 : S))).comp φ') := by
    change Function.Injective (((eval (fun _ => (0 : S))).comp tS).comp φ.toRingHom)
    have h0 : (eval (fun _ => (0 : S))).comp tS = eval (fun i => algebraMap K S (a i)) :=
      RingHom.ext (eval_zero_originShift _)
    rw [h0]
    exact hφ
  have hi := multivariate_deformation_injective φ' hφ'
  have he : tS.comp (eval₂Hom φ.toRingHom X) = (eval₂Hom φ' X).comp tR := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tR,originShift,φ']
    · intro i
      simp [tR,tS,originShift,φ']
  intro P Q h
  have ht : tS ((eval₂Hom φ.toRingHom X) P) =
      tS ((eval₂Hom φ.toRingHom X) Q) := congrArg tS h
  have ht' : (eval₂Hom φ' X) (tR P) = (eval₂Hom φ' X) (tR Q) := by
    simpa only [← RingHom.comp_apply,he] using ht
  exact originShift_injective _ (hi ht')

end
end CCDN

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
