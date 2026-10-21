/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CCDN.Algebra.RadialMap

/-!
Simultaneous polynomial deformation in arbitrarily many parameters.
Injectivity is detected by specialization of all parameters to zero.

A polynomial deformation whose constant specialization is injective
remains injective, including after adjoining the deformation parameters.
The proof uses the first nonzero coefficient.
-/

@[expose] public section
namespace CCDN
noncomputable section

private theorem polynomial_deformation_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* Polynomial S)
    (hφ : Function.Injective (Polynomial.constantCoeff.comp φ)) :
    Function.Injective (Polynomial.eval₂RingHom φ Polynomial.X) := by
  let Φ := Polynomial.eval₂RingHom φ Polynomial.X
  have hc : Polynomial.constantCoeff.comp Φ =
      (Polynomial.constantCoeff.comp φ).comp Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext'
    · ext r
      simp [Φ]
    · simp [Φ]
  apply (injective_iff_map_eq_zero Φ).mpr
  intro P hP
  by_contra hne
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun j hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (p := P) hj)
  have hQ0 : Q.coeff 0 ≠ 0 := by
    have hh := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hne
    have he : P.coeff P.natTrailingDegree = Q.coeff 0 := by
      calc
        P.coeff P.natTrailingDegree =
            (Polynomial.X ^ P.natTrailingDegree * Q).coeff (0 + P.natTrailingDegree) := by
          simpa only [Nat.zero_add] using congrArg (fun f : Polynomial R => f.coeff P.natTrailingDegree) hQ
        _ = Q.coeff 0 := Polynomial.coeff_X_pow_mul _ _ _
    rwa [he] at hh
  have hmapQ : Φ Q = 0 := by
    rw [hQ,map_mul,map_pow] at hP
    have hX : Φ Polynomial.X = Polynomial.X := by simp [Φ]
    rw [hX] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  have hz := RingHom.congr_fun hc Q
  rw [RingHom.comp_apply,hmapQ,map_zero] at hz
  have hzero : (Polynomial.constantCoeff.comp φ) (Q.coeff 0) = 0 := hz.symm
  exact hQ0 ((injective_iff_map_eq_zero (Polynomial.constantCoeff.comp φ)).mp hφ _ hzero)

end
end CCDN

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
