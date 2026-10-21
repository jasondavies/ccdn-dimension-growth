/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import CCDN.Algebra.OriginShift
import CCDN.Center.MultivariateDeformation
import Mathlib.Algebra.MvPolynomial.CommRing
/-! Specialization at an arbitrary parameter point detects injectivity of
a simultaneous polynomial deformation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem multivariate_deformation_injective_at
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
