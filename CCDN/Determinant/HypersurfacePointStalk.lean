/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Determinant.HypersurfaceHilbert
public import CCDN.Determinant.HypersurfaceOriginStalk
public import CCDN.Determinant.LocalizationAdicLayer
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.Determinant.HypersurfaceTangentEquality

/-!
Exact local Hilbert functions at arbitrary rational points of an affine
hypersurface, using the localization of its coordinate ring. The
translation to the origin and its action on all adic layers are constructed.

Algebra equivalences preserve ideal-adic layers.
-/

@[expose] public section
namespace CCDN
noncomputable section

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]

private def idealPowerLayerEquivOfEq {I J : Ideal A} (h : I = J) (k : ℕ) :
    Ideal.powerLayer K I k ≃ₗ[K] Ideal.powerLayer K J k := by
  subst J
  exact LinearEquiv.refl _ _

private def algEquivAdicQuotient (e : A ≃ₐ[K] B) (I : Ideal A) (N : ℕ) :
    (A ⧸ I ^ N) ≃ₐ[K] B ⧸ (I.map e.toRingHom) ^ N :=
  Ideal.quotientEquivAlg _ _ e (Ideal.map_pow e.toRingHom I N).symm

private lemma algEquivAdicQuotient_layer (e : A ≃ₐ[K] B) (I : Ideal A) (k : ℕ) :
    (Ideal.powerLayer K I k).map (algEquivAdicQuotient e I (k + 1)).toLinearMap =
      Ideal.powerLayer K (I.map e.toRingHom) k := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨e x, ?_, rfl⟩
    change e x ∈ (I.map e.toRingHom) ^ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    change y ∈ (I.map e.toRingHom) ^ k at hy
    rw [← Ideal.map_pow] at hy
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hy
    refine Submodule.mem_map.mpr ⟨Ideal.Quotient.mk _ x, ?_, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

private def algEquivAdicLayerEquiv (e : A ≃ₐ[K] B) (I : Ideal A) (k : ℕ) :
    Ideal.powerLayer K I k ≃ₗ[K] Ideal.powerLayer K (I.map e.toRingHom) k :=
  (Submodule.equivMapOfInjective (algEquivAdicQuotient e I (k + 1)).toLinearMap
    (algEquivAdicQuotient e I (k + 1)).injective _).trans
      (LinearEquiv.ofEq _ _ (algEquivAdicQuotient_layer e I k))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial IsLocalRing

variable {K : Type*} [Field K] {n : ℕ}

private lemma affineTranslation_map_pointIdeal (a : Fin n → K) :
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

/-- The `K`-algebra isomorphism between the coordinate rings of `f = 0` and of its translate
`affineTranslation K a f`, induced by the translation moving `a` to the origin. -/
def hypersurfaceTranslationEquiv (f : MvPolynomial (Fin n) K) (a : Fin n → K) :
    HypersurfaceCoordinateRing f ≃ₐ[K]
      HypersurfaceCoordinateRing (affineTranslation K a f) :=
  Ideal.quotientEquivAlg _ _ (affineTranslation K a)
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

/-- `hypersurfaceTranslationEquiv f a` sends the class of `g` to the class of its translate
`affineTranslation K a g`. -/
@[simp]
lemma hypersurfaceTranslationEquiv_apply_mk (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) (g : MvPolynomial (Fin n) K) :
    hypersurfaceTranslationEquiv f a (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (affineTranslation K a g) := rfl

/-- The ideal of the point `a` in the coordinate ring of the hypersurface `f = 0`. -/
def hypersurfacePointIdeal (f : MvPolynomial (Fin n) K) (a : Fin n → K) :
    Ideal (HypersurfaceCoordinateRing f) :=
  (RingHom.ker (eval a)).map (Ideal.Quotient.mk (Ideal.span {f}))

/-- If `a` lies on the hypersurface `f = 0`, its ideal in the coordinate ring is maximal. -/
lemma hypersurfacePointIdeal_isMaximal (f : MvPolynomial (Fin n) K)
    (a : Fin n → K) (hf : eval a f = 0) : (hypersurfacePointIdeal f a).IsMaximal := by
  let : (RingHom.ker (eval a)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, by simp⟩)
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact hf

private lemma hypersurfaceTranslationEquiv_map_pointIdeal (f : MvPolynomial (Fin n) K)
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

/-- The local ring of the affine hypersurface `f = 0` at a rational point `a` on it: the
localization of its coordinate ring at the maximal ideal of `a`. -/
abbrev HypersurfacePointStalk (f : MvPolynomial (Fin n) K) (a : Fin n → K)
    [Fact (eval a f = 0)] :=
  letI := (hypersurfacePointIdeal_isMaximal f a (Fact.out : eval a f = 0)).isPrime
  Localization.AtPrime (hypersurfacePointIdeal f a)

section Stalk

variable (f : MvPolynomial (Fin n) K) (a : Fin n → K) [Fact (eval a f = 0)]

local instance : (hypersurfacePointIdeal f a).IsMaximal :=
  hypersurfacePointIdeal_isMaximal f a Fact.out

/-- The local ring's layer at a is identified with the explicitly
computed origin layer of f(X+a). -/
private def hypersurfacePointStalkLayerEquiv (k : ℕ) :
    Ideal.powerLayer K (A := HypersurfacePointStalk f a)
      (maximalIdeal (HypersurfacePointStalk f a)) k ≃ₗ[K]
      originLayer (affineTranslation K a f) k := by
  let e := hypersurfaceTranslationEquiv f a
  let l := (localizationAdicLayerEquiv (K := K) (S := HypersurfacePointStalk f a)
    (hypersurfacePointIdeal f a) k).symm.trans
      (algEquivAdicLayerEquiv e (hypersurfacePointIdeal f a) k)
  have hi := hypersurfaceTranslationEquiv_map_pointIdeal f a
  let l' := l.trans (idealPowerLayerEquivOfEq (K := K) hi k)
  exact l'.trans (hypersurfaceCoordinateLayerEquiv (affineTranslation K a f) k)

/-- The degree-`k` layer of the maximal ideal of the local ring of `f = 0` at `a` has the same
`K`-dimension as the degree-`k` origin layer of the translated equation `affineTranslation K a f`.
-/
theorem hypersurfacePointStalkLayer_finrank (k : ℕ) :
    Module.finrank K (Ideal.powerLayer K (A := HypersurfacePointStalk f a)
      (maximalIdeal (HypersurfacePointStalk f a)) k) =
      Module.finrank K (originLayer (affineTranslation K a f) k) :=
  (hypersurfacePointStalkLayerEquiv f a k).finrank_eq

end Stalk

/-- `Ideal.powerLayer`, under the name used in the audited statement
`hypersurfacePointStalk_hilbert_eq`. -/
abbrev idealPowerLayer (K : Type*) [Field K] {A : Type*} [CommRing A] [Algebra K A]
    (I : Ideal A) (k : ℕ) : Submodule K (A ⧸ I ^ (k + 1)) :=
  Ideal.powerLayer K I k

/-- Exact binomial local Hilbert function at every K-rational point, in
every characteristic, with multiplicity given by its first form. -/
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
end CCDN
