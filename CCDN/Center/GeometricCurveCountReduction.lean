/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Center.GeometricCurveProjection
import CCDN.Projection.ProjectiveProjectionCount
import CCDN.ForMathlib.MvPolynomial
/-! An explicitly constructed geometrically integral plane curve has the
source degree and source function field of a projective curve, and satisfies
the additive point-count comparison of Propositions 4.3.1 and 4.3.2. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The projective curve clause of Proposition 4.3.2 on a proper standard
chart. The affine plane equation generates exactly the chart function field;
its projective closure stays irreducible after extending coefficients. -/
theorem exists_geometric_projective_curve_count_reduction_of_chart
    {L : Type*} [Field L] [Algebra ℚ L] {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hX : X 0 ∉ I) (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      let J := projectiveChartIdeal I
      let a := ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁]
      (∀ g, aeval a g ∈ J ↔ f ∣ g) ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (CoordinatePolynomial n ⧸ J)
          (FractionRing (CoordinatePolynomial n ⧸ J))
          ((Ideal.Quotient.mk J) (a i)))) = ⊤ ∧
      (scaledHomogenize d 1 f).IsHomogeneous d ∧
      Irreducible (scaledHomogenize d 1 f) ∧
      Irreducible (map (algebraMap ℚ L) (scaledHomogenize d 1 f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
          (projectionBoxFactor n d * B) + d ^ 2 := by
  let J := projectiveChartIdeal I
  let : (J.map (map (algebraMap ℚ L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime I hX
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) J d hd
      (projectiveChartIdeal_degree I hX hdegree)
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hfield,
    scaledHomogenize_homogeneous 1 f hfd.le, ?_, ?_, ?_⟩
  · simpa only [hfd] using scaledHomogenize_irreducible f hf one_ne_zero
  · rw [scaledHomogenize_map, map_one]
    have hdeg : (map (algebraMap ℚ L) f).totalDegree = d :=
      (totalDegree_map_of_injective (algebraMap ℚ L).injective _).trans hfd
    simpa only [hdeg] using scaledHomogenize_irreducible _ hfL one_ne_zero
  · exact projective_curve_count_le_of_moment_projection I hX hd hdegree f hfd hk₀ hk₁
      ((hker f).mpr dvd_rfl) hcount

end
end CCDN
