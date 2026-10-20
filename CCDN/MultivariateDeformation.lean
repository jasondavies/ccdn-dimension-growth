module

public import CCDN.PolynomialDeformation
public import Mathlib.Algebra.MvPolynomial.Basic

/-! Simultaneous polynomial deformation in arbitrarily many parameters.
Injectivity is detected by specialization of all parameters to zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def radialPolynomialMap (R σ : Type*) [CommRing R] :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C) (fun i => Polynomial.C (X i) * Polynomial.X)

lemma radialPolynomialMap_injective (R σ : Type*) [CommRing R] :
    Function.Injective (radialPolynomialMap R σ) := by
  have he : (Polynomial.evalRingHom 1).comp (radialPolynomialMap R σ) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [radialPolynomialMap]
    · intro i
      simp [radialPolynomialMap]
  exact Function.LeftInverse.injective (fun p => RingHom.congr_fun he p)

lemma radialPolynomialMap_constantCoeff (R σ : Type*) [CommRing R] :
    Polynomial.constantCoeff.comp (radialPolynomialMap R σ) =
      C.comp (eval (fun _ => (0 : R))) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [radialPolynomialMap]
  · intro i
    simp [radialPolynomialMap]

/-- A polynomial coefficient substitution with injective constant
specialization stays injective while keeping all parameter variables. -/
theorem multivariate_deformation_injective
    {R S σ : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* MvPolynomial σ S)
    (hφ : Function.Injective ((eval (fun _ => (0 : S))).comp φ)) :
    Function.Injective (eval₂Hom φ X) := by
  let ψ : MvPolynomial σ R →+* Polynomial (MvPolynomial σ S) :=
    eval₂Hom ((radialPolynomialMap S σ).comp φ) (fun i => Polynomial.C (X i))
  have hc : Polynomial.constantCoeff.comp ψ =
      map ((eval (fun _ => (0 : S))).comp φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,ψ,eval₂Hom_C]
      change (Polynomial.constantCoeff.comp (radialPolynomialMap S σ)) (φ r) = _
      rw [radialPolynomialMap_constantCoeff]
      simp
    · intro i
      simp [ψ]
  have hψ : Function.Injective (Polynomial.constantCoeff.comp ψ) := by
    rw [hc]
    exact MvPolynomial.map_injective _ hφ
  let Ψ := Polynomial.eval₂RingHom ψ Polynomial.X
  have hΨ : Function.Injective Ψ := polynomial_deformation_injective ψ hψ
  have he : Ψ.comp (radialPolynomialMap R σ) =
      (radialPolynomialMap S σ).comp (eval₂Hom φ X) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Ψ,ψ,radialPolynomialMap]
    · intro i
      simp [Ψ,ψ,radialPolynomialMap]
  apply (injective_iff_map_eq_zero (eval₂Hom φ X)).mpr
  intro P hP
  have hz : Ψ (radialPolynomialMap R σ P) = 0 := by
    have hh := RingHom.congr_fun he P
    simpa only [RingHom.comp_apply,hP,map_zero] using hh
  exact (radialPolynomialMap_injective R σ)
    ((injective_iff_map_eq_zero Ψ).mp hΨ _ hz |>.trans (map_zero _).symm)

end
end CCDN
