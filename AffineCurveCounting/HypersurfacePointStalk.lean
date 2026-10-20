module

public import AffineCurveCounting.HypersurfaceOriginStalk
public import AffineCurveCounting.AlgEquivAdicLayer
public import AffineCurveCounting.AffineTranslationCount
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Exact local Hilbert functions at arbitrary rational points of an affine
hypersurface, using the actual localization of its coordinate ring. The
translation to the origin and its action on all adic layers are constructed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial IsLocalRing

variable {K : Type*} [Field K] {n : ℕ}

lemma affineTranslation_map_pointIdeal (a : Fin n → K) :
    (RingHom.ker (eval a)).map (affineTranslation K a).toRingHom =
      idealOfVars (Fin n) K := by
  rw [idealOfVars_eq_ker_constantCoeff]
  ext g
  have hsurj : Function.Surjective (affineTranslation K a).toRingHom :=
    (affineTranslation K a).surjective
  rw [Ideal.mem_map_iff_of_surjective _ hsurj]
  constructor
  · rintro ⟨f, hf, rfl⟩
    change constantCoeff (affineTranslation K a f) = 0
    rw [constantCoeff_eq, affineTranslation_constantCoeff]
    exact hf
  · intro hg
    refine ⟨(affineTranslation K a).symm g, ?_, (affineTranslation K a).apply_symm_apply g⟩
    change eval a ((affineTranslation K a).symm g) = 0
    rw [← affineTranslation_constantCoeff, AlgEquiv.apply_symm_apply]
    exact hg

def hypersurfaceTranslationEquiv (f : MvPolynomial (Fin n) K) (a : Fin n → K) :
    HypersurfaceCoordinateRing f ≃ₐ[K]
      HypersurfaceCoordinateRing (affineTranslation K a f) :=
  Ideal.quotientEquivAlg _ _ (affineTranslation K a)
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

@[simp]
lemma hypersurfaceTranslationEquiv_apply_mk (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) (g : MvPolynomial (Fin n) K) :
    hypersurfaceTranslationEquiv f a (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (affineTranslation K a g) := rfl

def hypersurfacePointIdeal (f : MvPolynomial (Fin n) K) (a : Fin n → K) :
    Ideal (HypersurfaceCoordinateRing f) :=
  (RingHom.ker (eval a)).map (Ideal.Quotient.mk (Ideal.span {f}))

lemma hypersurfacePointIdeal_isMaximal (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) (hf : eval a f = 0) : (hypersurfacePointIdeal f a).IsMaximal := by
  let : (RingHom.ker (eval a)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact hf

/-- The residue field at the rational point is canonically the coefficient
field, as an algebra over that field. -/
def hypersurfacePointCoordinateResidueEquiv (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) (hf : eval a f = 0) :
    (HypersurfaceCoordinateRing f ⧸ hypersurfacePointIdeal f a) ≃ₐ[K] K := by
  let φ : MvPolynomial (Fin n) K →ₐ[K] K :=
    { eval a with commutes' := fun c => by simp }
  have hspan : Ideal.span {f} ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact hf
  exact (DoubleQuot.quotQuotEquivQuotOfLEₐ K hspan).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := φ) (fun c => ⟨C c, by simp [φ]⟩))

lemma hypersurfaceTranslationEquiv_map_pointIdeal (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) :
    (hypersurfacePointIdeal f a).map (hypersurfaceTranslationEquiv f a).toRingHom =
      hypersurfaceOriginIdeal (affineTranslation K a f) := by
  have he : (hypersurfaceTranslationEquiv f a).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {f})) =
      (Ideal.Quotient.mk (Ideal.span {affineTranslation K a f})).comp
        (affineTranslation K a).toRingHom := by
    apply RingHom.ext
    intro g
    exact hypersurfaceTranslationEquiv_apply_mk f a g
  rw [hypersurfacePointIdeal, Ideal.map_map, he, ← Ideal.map_map,
    affineTranslation_map_pointIdeal]
  rfl

abbrev HypersurfacePointStalk (f : MvPolynomial (Fin n) K) (a : Fin n → K)
    [Fact (eval a f = 0)] :=
  letI := (hypersurfacePointIdeal_isMaximal f a (Fact.out : eval a f = 0)).isPrime
  Localization.AtPrime (hypersurfacePointIdeal f a)

section Stalk

variable (f : MvPolynomial (Fin n) K) (a : Fin n → K) [Fact (eval a f = 0)]

local instance : (hypersurfacePointIdeal f a).IsMaximal :=
  hypersurfacePointIdeal_isMaximal f a Fact.out

def hypersurfacePointStalkResidueEquiv :
    ResidueField (HypersurfacePointStalk f a) ≃ₐ[K] K :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal
    (hypersurfacePointIdeal f a) (HypersurfacePointStalk f a)).restrictScalars K).symm.trans
      (hypersurfacePointCoordinateResidueEquiv f a Fact.out)

/-- The local ring's actual layer at a is identified with the explicitly
computed origin layer of f(X+a). -/
def hypersurfacePointStalkLayerEquiv (k : ℕ) :
    idealPowerLayer K (A := HypersurfacePointStalk f a)
      (maximalIdeal (HypersurfacePointStalk f a)) k ≃ₗ[K]
      originLayer (affineTranslation K a f) k := by
  let e := hypersurfaceTranslationEquiv f a
  let l := (localizationAdicLayerEquiv (K := K) (S := HypersurfacePointStalk f a)
    (hypersurfacePointIdeal f a) k).symm.trans
      (algEquivAdicLayerEquiv e (hypersurfacePointIdeal f a) k)
  have hi := hypersurfaceTranslationEquiv_map_pointIdeal f a
  let l' := l.trans (idealPowerLayerEquivOfEq (K := K) hi k)
  exact l'.trans (hypersurfaceCoordinateLayerEquiv (affineTranslation K a f) k)

theorem hypersurfacePointStalkLayer_finrank (k : ℕ) :
    Module.finrank K (idealPowerLayer K (A := HypersurfacePointStalk f a)
      (maximalIdeal (HypersurfacePointStalk f a)) k) =
      Module.finrank K (originLayer (affineTranslation K a f) k) :=
  (hypersurfacePointStalkLayerEquiv f a k).finrank_eq

end Stalk

/-- Exact binomial local Hilbert function at every K-rational point, in
every characteristic, with multiplicity given by its actual first form. -/
theorem hypersurfacePointStalk_hilbert_eq {μ k : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (a : Fin (n + 1) → K)
    [Fact (eval a f = 0)]
    (hf : affineTranslation K a f ∈ idealOfVars (Fin (n + 1)) K ^ μ)
    (hμ : homogeneousComponent μ (affineTranslation K a f) ≠ 0) :
    Module.finrank K (idealPowerLayer K (A := HypersurfacePointStalk f a)
      (maximalIdeal (HypersurfacePointStalk f a)) k) =
      hypersurfaceLayerBound n μ k := by
  rw [hypersurfacePointStalkLayer_finrank]
  exact originLayer_finrank_eq_hypersurfaceLayerBound _ hf hμ

end
end AffineCurveCounting
