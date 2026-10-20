module

public import CCDN.MultivariateDeformation

/-! Specialization at an arbitrary parameter point detects injectivity of
a simultaneous polynomial deformation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def parameterTranslation {R σ : Type*} [CommRing R] (a : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (a i))

lemma parameterTranslation_injective {R σ : Type*} [CommRing R] (a : σ → R) :
    Function.Injective (parameterTranslation a) := by
  have he : (parameterTranslation (-a)).comp (parameterTranslation a) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [parameterTranslation]
    · intro i
      simp [parameterTranslation]
  have hi : Function.LeftInverse (parameterTranslation (-a)) (parameterTranslation a) :=
    fun P => RingHom.congr_fun he P
  exact hi.injective

lemma eval_zero_parameterTranslation {R σ : Type*} [CommRing R] (a : σ → R) :
    (eval (fun _ => 0)).comp (parameterTranslation a) = eval a := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [parameterTranslation]
  · intro i
    simp [parameterTranslation]

theorem multivariate_deformation_injective_at
    {K R S σ : Type*} [CommRing K] [CommRing R] [CommRing S] [IsDomain S]
    [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] MvPolynomial σ S) (a : σ → K)
    (hφ : Function.Injective ((eval (fun i => algebraMap K S (a i))).comp φ.toRingHom)) :
    Function.Injective (eval₂Hom φ.toRingHom X) := by
  let tS := parameterTranslation (fun i => algebraMap K S (a i))
  let tR := parameterTranslation (fun i => algebraMap K R (a i))
  let φ' := tS.comp φ.toRingHom
  have hφ' : Function.Injective ((eval (fun _ => (0 : S))).comp φ') := by
    change Function.Injective (((eval (fun _ => (0 : S))).comp tS).comp φ.toRingHom)
    rw [eval_zero_parameterTranslation]
    exact hφ
  have hi := multivariate_deformation_injective φ' hφ'
  have he : tS.comp (eval₂Hom φ.toRingHom X) = (eval₂Hom φ' X).comp tR := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tR,parameterTranslation,φ']
    · intro i
      simp [tR,tS,parameterTranslation,φ']
  intro P Q h
  have ht : tS ((eval₂Hom φ.toRingHom X) P) =
      tS ((eval₂Hom φ.toRingHom X) Q) := congrArg tS h
  have ht' : (eval₂Hom φ' X) (tR P) = (eval₂Hom φ' X) (tR Q) := by
    simpa only [← RingHom.comp_apply,he] using ht
  exact parameterTranslation_injective _ (hi ht')

end
end CCDN
