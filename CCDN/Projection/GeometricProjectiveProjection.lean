/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.ProjectionScalarExtension
import CCDN.Projection.ProjectiveVarietyProjection
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
  obtain ⟨b, f, hP, hfhom, hfdeg, hcount⟩ :=
    exists_projective_variety_projection m n hmn I hI d hd hdimdeg
  exact ⟨b, hP.integral, hP.birational, f, hP.irreducible,
    projection_equation_irreducible_map I _ f hP.irreducible.ne_zero hP.ker_eq,
    hfhom, hfdeg, hP.ker_eq, hcount⟩

end
end CCDN
