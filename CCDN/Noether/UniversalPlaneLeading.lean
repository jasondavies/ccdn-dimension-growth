/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineLineLeading
public import CCDN.Noether.UniversalPlaneFamily
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Auxiliary.HypersurfacePositioning
import CCDN.Noether.UniversalPlaneWitness
import CCDN.Projection.ShearNormalization
import CCDN.ForMathlib.MvPolynomial
/-! The leading coefficient of a universal plane section detects loss of the
full outer degree. It is evaluated by the highest homogeneous form in the
first direction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma universalPlanePolynomial_specialize_axis {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    Polynomial.map (Polynomial.evalRingHom 0)
      (bivariateMap (planeParameterEval (RingHom.id K) a b c) (universalPlanePolynomial f)) =
      affineLinePolynomial a b f := by
  rw [universalPlanePolynomial_specialize]
  have he : (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
      ((bivariatePolynomialEquiv K).toRingHom.comp
        (eval₂Hom (C.comp (RingHom.id K))
          (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1))) = affineLinePolynomial a b := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affineLinePolynomial, bivariatePolynomialEquiv_C]
    · intro i
      simp [affineLinePolynomial, bivariatePolynomialEquiv_C,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- The coefficient of x^d y^0, as a polynomial in all plane parameters. -/
def universalPlaneLeading {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    MvPolynomial (PlaneParameters σ) K :=
  ((universalPlanePolynomial f).coeff f.totalDegree).coeff 0

lemma universalPlaneLeading_specialize {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    planeParameterEval (RingHom.id K) a b c (universalPlaneLeading f) =
      eval b (homogeneousComponent f.totalDegree f) := by
  have h := congrArg (fun q : Polynomial K => q.coeff f.totalDegree)
    (universalPlanePolynomial_specialize_axis a b c f)
  rw [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h
  change Polynomial.eval 0 ((bivariateMap (planeParameterEval (RingHom.id K) a b c)
    (universalPlanePolynomial f)).coeff f.totalDegree) = _ at h
  rw [← Polynomial.coeff_zero_eq_eval_zero, bivariateMap_coeff] at h
  exact h

lemma universalPlaneLeading_map {K L σ : Type*} [Field K] [Field L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneLeading (MvPolynomial.map φ f) = MvPolynomial.map φ (universalPlaneLeading f) := by
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  simp only [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]

/-- Geometric irreducibility and the characteristic bound suffice for the
leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero
    {K σ : Type*} [Field K] [Fintype σ] {p : ℕ} [CharP K p]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : 2 * f.totalDegree ^ 2 < p) :
    universalPlaneLeading f ≠ 0 := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  have : CharP L p := charP_of_injective_algebraMap φ.injective p
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hdp : (MvPolynomial.map φ f).totalDegree < p := by rw [ht]; nlinarith
  obtain ⟨a, b, _, hdir, _⟩ := exists_monic_smooth_hypersurface_coordinates
    (MvPolynomial.map φ f) hf (ht ▸ hpos) hdp
  intro hz
  apply hdir
  rw [← universalPlaneLeading_specialize a b 0, universalPlaneLeading_map, hz, map_zero, map_zero]

end
end CCDN
