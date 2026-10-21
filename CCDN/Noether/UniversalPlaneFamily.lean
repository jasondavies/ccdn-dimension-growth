/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.ClosedFormScaling
import CCDN.Projection.ShearNormalization
/-! The universal affine two-plane, with independent coordinates for its base
point and both directions. Its specializations are affine-plane
restrictions; its polynomial coefficients are the objects to be counted. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

abbrev PlaneParameters (σ : Type*) := σ × Fin 3

/-- All affine planes a+x*b+y*c, with every coordinate an independent parameter. -/
def universalPlaneMap (K σ : Type*) [CommRing K] :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Fin 2) (MvPolynomial (PlaneParameters σ) K) :=
  aeval (fun i => C (X (i,0)) + C (X (i,1)) * X 0 + C (X (i,2)) * X 1)

def universalPlanePolynomial {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    Polynomial (Polynomial (MvPolynomial (PlaneParameters σ) K)) :=
  bivariatePolynomialEquiv _ (universalPlaneMap K σ f)

/-- Evaluate all three blocks of affine-plane parameters. -/
def planeParameterEval {K A σ : Type*} [CommRing K] [CommRing A]
    (φ : K →+* A) (a b c : σ → A) : MvPolynomial (PlaneParameters σ) K →+* A :=
  eval₂Hom φ (fun i => ![a i.1, b i.1, c i.1] i.2)

/-- Universal specialization is exactly the displayed affine substitution. -/
theorem universalPlaneMap_specialize {K A σ : Type*} [CommRing K] [CommRing A]
    (φ : K →+* A) (a b c : σ → A) (f : MvPolynomial σ K) :
    MvPolynomial.map (planeParameterEval φ a b c) (universalPlaneMap K σ f) =
      eval₂Hom (C.comp φ) (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) f := by
  have he : (MvPolynomial.map (planeParameterEval φ a b c)).comp (universalPlaneMap K σ).toRingHom =
      eval₂Hom (C.comp φ) (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalPlaneMap, planeParameterEval]
    · intro i
      simp [universalPlaneMap, planeParameterEval]
  exact RingHom.congr_fun he f

lemma universalPlanePolynomial_specialize {K A σ : Type*} [CommRing K] [CommRing A]
    (φ : K →+* A) (a b c : σ → A) (f : MvPolynomial σ K) :
    bivariateMap (planeParameterEval φ a b c) (universalPlanePolynomial f) =
      bivariatePolynomialEquiv A
        (eval₂Hom (C.comp φ) (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) f) := by
  rw [universalPlanePolynomial, bivariatePolynomialEquiv_map, universalPlaneMap_specialize]

lemma closedForm_minor_smul {R : Type*} [CommRing R]
    (u : R) (d r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    ((closedFormCoefficientMatrix d (u • f)).submatrix a c).det =
      u ^ r * ((closedFormCoefficientMatrix d f).submatrix a c).det := by
  rw [closedFormCoefficientMatrix_smul]
  change (u • (closedFormCoefficientMatrix d f).submatrix a c).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

end
end CCDN
