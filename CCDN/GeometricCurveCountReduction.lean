module

public import CCDN.GeometricCurveProjection
public import CCDN.ProjectiveChartScalarExtension
public import CCDN.AffineProjectionCount
public import CCDN.ProjectiveProjectionCount

/-! The same explicitly constructed geometrically integral plane curve
has the source degree, source function field and the additive point-count
comparison in Propositions 4.3.1 and 4.3.2. -/

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
      (boundedHomogenize d f).IsHomogeneous d ∧
      Irreducible (boundedHomogenize d f) ∧
      Irreducible (map (algebraMap ℚ L) (boundedHomogenize d f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (boundedHomogenize d f))
          (projectionBoxFactor n d * B) + d ^ 2 := by
  let J := projectiveChartIdeal I
  let : (J.map (map (algebraMap ℚ L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime I hX
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) J d hd
      (projectiveChartIdeal_degree I hX hdegree)
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hfield,
    boundedHomogenize_homogeneous f hfd.le, ?_, ?_, ?_⟩
  · simpa only [hfd] using boundedHomogenize_irreducible f hf
  · rw [← scaledHomogenize_one, scaledHomogenize_map, map_one, scaledHomogenize_one]
    have hdeg : (map (algebraMap ℚ L) f).totalDegree = d := by
      unfold totalDegree
      rw [support_map_of_injective _ (algebraMap ℚ L).injective]
      exact hfd
    simpa only [hdeg] using boundedHomogenize_irreducible _ hfL
  · exact projective_curve_count_le_of_moment_projection I hX hd hdegree f hfd hk₀ hk₁
      ((hker f).mpr dvd_rfl) hcount

end
end CCDN
