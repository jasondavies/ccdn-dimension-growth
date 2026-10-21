/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Noether.ClosedFormScaling
import CCDN.Noether.ShearNormalization

/-!
# The universal affine plane

The universal affine two-plane has independent coordinates for its base point and both
directions. Its specializations are affine-plane restrictions; its polynomial coefficients are
the objects to be counted. Every coefficient of the universal restriction has degree in the
plane parameters bounded by the total degree of the original equation.
-/

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

namespace CCDN
noncomputable section
open MvPolynomial

lemma commAlgEquiv_coeff_coeff {K σ τ : Type*} [CommRing K]
    (f : MvPolynomial σ (MvPolynomial τ K)) (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    ((commAlgEquiv K σ τ f).coeff n).coeff m = (f.coeff m).coeff n := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial a b =>
    induction b using MvPolynomial.induction_on' with
    | add b c hb hc => simp [hb, hc]
    | monomial b c =>
      simp [commAlgEquiv, monomial, AddMonoidAlgebra.commAlgEquiv_single_single,
        Finsupp.single_apply, eq_comm]
      split_ifs <;> simp_all [AddMonoidAlgebra.coeff_single]

private lemma coefficient_totalDegree_le_commAlgEquiv {K σ τ : Type*} [CommRing K]
    (f : MvPolynomial σ (MvPolynomial τ K)) (m : σ →₀ ℕ) :
    (f.coeff m).totalDegree ≤ (commAlgEquiv K σ τ f).totalDegree := by
  classical
  apply Finset.sup_le
  intro n hn
  apply le_totalDegree
  rw [mem_support_iff] at hn ⊢
  intro he
  apply hn
  rw [← commAlgEquiv_coeff_coeff, he]
  rfl

private lemma universalPlaneMap_comm {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    commAlgEquiv K (Fin 2) (PlaneParameters σ) (universalPlaneMap K σ f) =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin 2) K))
        (fun i => X (i,0) + X (i,1) * C (X 0) + X (i,2) * C (X 1)) f := by
  have he : (commAlgEquiv K (Fin 2) (PlaneParameters σ)).toRingHom.comp
      (universalPlaneMap K σ).toRingHom =
      eval₂Hom (C.comp (C : K →+* MvPolynomial (Fin 2) K))
        (fun i => X (i,0) + X (i,1) * C (X 0) + X (i,2) * C (X 1)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalPlaneMap]
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

private lemma universalPlaneMap_parameterDegree_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) :
    (commAlgEquiv K (Fin 2) (PlaneParameters σ) (universalPlaneMap K σ f)).totalDegree ≤
      f.totalDegree := by
  rw [universalPlaneMap_comm]
  apply linear_eval₂_totalDegree_le
  intro i
  have hx (j : PlaneParameters σ) :
      (X j : MvPolynomial (PlaneParameters σ) (MvPolynomial (Fin 2) K)).totalDegree ≤ 1 := by
    simpa [X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : MvPolynomial (Fin 2) K)
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact hx _
    · exact (totalDegree_mul _ _).trans (by simpa using hx (i,1))
  · exact (totalDegree_mul _ _).trans (by simpa using hx (i,2))

/-- Each coefficient has degree at most d in ALL plane parameters together. -/
theorem universalPlanePolynomial_coefficient_degree {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (i j : ℕ) :
    (((universalPlanePolynomial f).coeff i).coeff j).totalDegree ≤ f.totalDegree := by
  rw [universalPlanePolynomial, bivariatePolynomialEquiv_coeff]
  exact (coefficient_totalDegree_le_commAlgEquiv _ _).trans
    (universalPlaneMap_parameterDegree_le f)

end
end CCDN
