module

public import CCDN.Surface.ProjectiveSurfaceSalbergerCover
public import CCDN.Determinant.ProjectiveChartSmoothness
public import CCDN.Algebra.PolynomialPredicates
/-! CCDN Theorem 4.3.5 with projective curve ideals, their projective
Hilbert degrees, and the homogeneous Jacobian definition of nonsingular
points in the standard affine chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem salberger_surface_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (F : CoordinatePolynomial 4), F.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      (¬ X 0 ∣ F) → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 4)))
        (δ : Ideal (CoordinatePolynomial 4) → ℕ),
        (∀ J ∈ S, J.IsPrime ∧
          IsHomogeneousIdeal J ∧
          (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
          F ∈ J ∧ X 0 ∉ J ∧ 0 < δ J ∧ HasProjectiveCurveDegree J (δ J) ∧ δ J ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (projectiveSmoothAffineChart F \
          affineProjectivePoint ⁻¹' (⋃ J ∈ S, projectiveIdealZeroLocus J)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  obtain ⟨C,c,hC,hc,hcover⟩ := projective_surface_salberger_cover d hd
  refine ⟨C,c,hC,hc,?_⟩
  intro F hhom habs hX B hB
  obtain ⟨S,δ,hS,hcard,hcount⟩ := hcover F hhom habs hX B hB
  exact ⟨S,δ,hS,hcard,by simpa only [projectiveSmoothAffineChart_eq F hhom] using hcount⟩

end
end CCDN
