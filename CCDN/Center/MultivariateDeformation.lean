/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Coeff
import CCDN.Algebra.RadialMap
import CCDN.Center.PolynomialDeformation

/-! Simultaneous polynomial deformation in arbitrarily many parameters.
Injectivity is detected by specialization of all parameters to zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A polynomial coefficient substitution with injective constant
specialization stays injective while keeping all parameter variables. -/
theorem multivariate_deformation_injective
    {R S σ : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* MvPolynomial σ S)
    (hφ : Function.Injective ((eval (fun _ => (0 : S))).comp φ)) :
    Function.Injective (eval₂Hom φ X) := by
  let ψ : MvPolynomial σ R →+* Polynomial (MvPolynomial σ S) :=
    eval₂Hom ((radialMap : MvPolynomial σ S →+* _).comp φ) (fun i => Polynomial.C (X i))
  have hc : Polynomial.constantCoeff.comp ψ =
      map ((eval (fun _ => (0 : S))).comp φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,ψ,eval₂Hom_C]
      change (Polynomial.constantCoeff.comp (radialMap : MvPolynomial σ S →+* _)) (φ r) = _
      rw [constantCoeff_comp_radialMap]
      simp
    · intro i
      simp [ψ]
  have hψ : Function.Injective (Polynomial.constantCoeff.comp ψ) := by
    rw [hc]
    exact MvPolynomial.map_injective _ hφ
  let Ψ := Polynomial.eval₂RingHom ψ Polynomial.X
  have hΨ : Function.Injective Ψ := polynomial_deformation_injective ψ hψ
  have he : Ψ.comp (radialMap : MvPolynomial σ R →+* _) =
      (radialMap : MvPolynomial σ S →+* _).comp (eval₂Hom φ X) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Ψ,ψ,radialMap]
    · intro i
      simp [Ψ,ψ,radialMap]
  apply (injective_iff_map_eq_zero (eval₂Hom φ X)).mpr
  intro P hP
  have hz : Ψ ((radialMap : MvPolynomial σ R →+* _) P) = 0 := by
    have hh := RingHom.congr_fun he P
    simpa only [RingHom.comp_apply,hP,map_zero] using hh
  exact (radialMap_injective (K := R) (σ := σ))
    ((injective_iff_map_eq_zero Ψ).mp hΨ _ hz |>.trans (map_zero _).symm)

end
end CCDN
