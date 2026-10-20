module

public import CCDN.GenericPlaneIrreducibility
public import CCDN.PlaneSmoothGeometricIrreducibility

/-! The generic plane f(x,y*z), with slopes in their rational function
field, has a smooth origin whenever the original equation does. Together with
ordinary irreducibility this proves geometric irreducibility of the generic
plane in the positioned coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The generic plane substitution as a map of multivariate polynomial rings. -/
def genericPlaneMap (K F σ : Type*) [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F] :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Fin 2) F :=
  aeval (fun i => Option.elim i (X 0)
    (fun j => C (algebraMap (MvPolynomial σ K) F (X j)) * X 1))

lemma genericPlaneMap_bivariate {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    bivariatePolynomialEquiv F (genericPlaneMap K F σ f) =
      bivariateMap (algebraMap (MvPolynomial σ K) F) (genericPlanePolynomial f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
      bivariateMap, bivariatePolynomialEquiv_C]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial σ K) F a
  | add f g hf hg =>
    simp only [map_add, hf, hg, genericPlanePolynomial, Polynomial.map_add]
  | mul_X f i hf =>
    cases i <;>
      simp [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
        bivariateMap, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariatePolynomialEquiv_C] at hf ⊢
    all_goals simp only [hf, true_or]

lemma genericPlaneMap_eval_zero {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    eval (0 : Fin 2 → F) (genericPlaneMap K F σ f) =
      algebraMap K F (eval (0 : Option σ → K) f) := by
  have he : (eval (0 : Fin 2 → F)).comp (genericPlaneMap K F σ).toRingHom =
      (algebraMap K F).comp (eval (0 : Option σ → K)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericPlaneMap]
    · intro i
      cases i <;> simp [genericPlaneMap]
  exact RingHom.congr_fun he f

lemma genericPlaneMap_pderiv {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    pderiv 0 (genericPlaneMap K F σ f) = genericPlaneMap K F σ (pderiv none f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [genericPlaneMap]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    cases i <;> simp [genericPlaneMap, pderiv_X] at hf ⊢
    all_goals simp only [hf, true_or]

/-- Ordinary irreducibility over the rational function field in slopes. -/
theorem genericPlaneMap_irreducible
    {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree) :
    Irreducible (genericPlaneMap K F σ f) := by
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mp
  rw [genericPlaneMap_bivariate]
  exact genericPlanePolynomial_irreducible_fraction_slopes f hf hd hm hx

/-- The generic plane stays irreducible over every extension of its slope field
when the original hypersurface has a smooth origin in the distinguished direction. -/
theorem genericPlaneMap_geometrically_irreducible
    {K F L σ : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra (MvPolynomial σ K) F] [Algebra F L]
    [IsScalarTower K (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    Irreducible (MvPolynomial.map (algebraMap F L) (genericPlaneMap K F σ f)) := by
  apply irreducible_map_of_smooth_plane_point _
    (genericPlaneMap_irreducible f hf hd hm hx) (0 : Fin 2 → F) 0
  · rw [genericPlaneMap_eval_zero, hz, map_zero]
  · rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    exact (map_ne_zero (algebraMap K F)).mpr hs

end
end CCDN
