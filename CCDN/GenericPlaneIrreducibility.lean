module

public import CCDN.GenericPlaneStretch
public import CCDN.ShearNormalization

/-! Ordinary irreducibility of f(x,y*z_1,...,y*z_n) over the rational function
field in the slopes z_i. The original equation is irreducible and monic in x;
all parameter extensions and changes of polynomial presentation are proved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Exchange the fresh y parameter with the transverse slope variables. -/
def genericPlaneCoefficientEquiv (K σ : Type*) [Field K] :
    MvPolynomial σ (MvPolynomial Unit K) ≃ₐ[K] Polynomial (MvPolynomial σ K) :=
  (commAlgEquiv K σ Unit).trans ((uniqueAlgEquiv (MvPolynomial σ K) Unit).restrictScalars K)

/-- Replace each transverse variable z_i with the polynomial z_i*y. -/
def genericPlaneCoefficients (K σ : Type*) [Field K] :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval (fun i => Polynomial.C (X i) * Polynomial.X)

/-- The generic plane equation, with x outermost and y the inner variable. -/
def genericPlanePolynomial {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) : Polynomial (Polynomial (MvPolynomial σ K)) :=
  Polynomial.map (genericPlaneCoefficients K σ).toRingHom (optionEquivLeft K σ f)

lemma genericPlaneCoefficientEquiv_stretch {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) :
    Polynomial.map (genericPlaneCoefficientEquiv K σ).toRingHom (genericPlaneStretch f) =
      genericPlanePolynomial f := by
  have he : (genericPlaneCoefficientEquiv K σ).toRingHom.comp
      (genericStretchCoefficients K σ).toRingHom = (genericPlaneCoefficients K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericPlaneCoefficientEquiv, genericStretchCoefficients, genericPlaneCoefficients]
    · intro i
      simp [genericPlaneCoefficientEquiv, genericStretchCoefficients, genericPlaneCoefficients]
  simp only [genericPlaneStretch, genericPlanePolynomial, Polynomial.map_map, he]

lemma genericPlanePolynomial_monic {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).Monic := hf.map _

lemma genericPlanePolynomial_natDegree {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (hf : (optionEquivLeft K σ f).Monic) :
    (genericPlanePolynomial f).natDegree = (optionEquivLeft K σ f).natDegree :=
  hf.natDegree_map _

/-- The joint polynomial in x, y and all slope variables is irreducible. -/
theorem genericPlanePolynomial_irreducible {K σ : Type*} [Field K]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic) :
    Irreducible (genericPlanePolynomial f) := by
  rw [← genericPlaneCoefficientEquiv_stretch]
  exact (MulEquiv.irreducible_iff
    (f := Polynomial.mapAlgEquiv (genericPlaneCoefficientEquiv K σ))).mpr
      (genericPlaneStretch_irreducible f hf hd hm)

/-- Localizing the slope parameters preserves the ordinary irreducibility of
the actual generic plane equation. -/
theorem genericPlanePolynomial_irreducible_fraction_slopes
    {K F σ : Type*} [Field K] [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree) :
    Irreducible (bivariateMap (algebraMap (MvPolynomial σ K) F) (genericPlanePolynomial f)) := by
  let R := MvPolynomial σ K
  let g := (bivariatePolynomialEquiv R).symm (genericPlanePolynomial f)
  have hg : Irreducible g :=
    (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv R).symm)).mpr
      (genericPlanePolynomial_irreducible f hf hd hm)
  have hgdeg : 0 < g.totalDegree := by
    have hh := bivariate_natDegree_le_totalDegree (genericPlanePolynomial f)
    rw [genericPlanePolynomial_natDegree f hm] at hh
    exact hx.trans_le hh
  have hp := prime_mvPolynomial_map_localization (S := F) (nonZeroDivisors R)
    le_rfl g hg.prime hgdeg
  have he := (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mpr hp.irreducible
  rw [← bivariatePolynomialEquiv_map] at he
  simpa only [g, AlgEquiv.apply_symm_apply] using he

end
end CCDN
