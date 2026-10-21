module

public import CCDN.Projection.ProjectionScalarExtension
public import CCDN.Projection.ProjectiveVarietyProjection
public import CCDN.Algebra.PolynomialPredicates
/-! Geometric integrality in the finite birational projective
projection. This supplies the general-dimensional geometric interface of
Proposition 4.3.2, with a dimension-only polynomial height cost. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The constructed finite birational integer projection preserves degree
and geometric integrality, and its point-count comparison has factor
exactly `d`. Scalar extension may be to any field where the source stays
prime, in particular to an algebraic closure. -/
theorem exists_geometrically_integral_projective_projection
    {L : Type*} [Field L] [Algebra ℚ L]
    (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hd : 1 ≤ d)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin (n + 1) → ℤ,
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ Irreducible (map (algebraMap ℚ L) f) ∧
        f.IsHomogeneous d ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, projectiveCount (projectiveIdealZeroLocus I) B ≤
          d * projectiveCount (projectiveZeroLocus f)
            (((n + 1 : ℕ) * birationalProjectionHeightConstant (n + 1) : ℕ) *
              (d : ℝ) ^ (2 * (n + 1)) * B) := by
  obtain ⟨b, hint, hfield, f, hf, hfhom, hfdeg, hker, hcount⟩ :=
    exists_projective_variety_projection m n hmn I hI d hd hdimdeg
  exact ⟨b, hint, hfield, f, hf,
    projection_equation_irreducible_map I _ f hf.ne_zero hker,
    hfhom, hfdeg, hker, hcount⟩

end
end CCDN
