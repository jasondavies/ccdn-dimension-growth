module

public import AffineCurveCounting.ProjectionScalarExtension
public import AffineCurveCounting.SharpProjectiveProjection

/-! Geometric integrality in the actual finite birational projective
projection. This supplies the general-dimensional geometric interface of
Proposition 4.3.2, with a dimension-only polynomial height cost. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The constructed finite birational integer projection preserves degree
and geometric integrality, and its actual point-count comparison has factor
exactly `d`. Scalar extension may be to any field where the source stays
prime, in particular to an algebraic closure. -/
theorem exists_geometrically_integral_projective_projection
    {L : Type*} [Field L] [Algebra ℚ L]
    (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I)
    (d : ℕ) (hd : 1 ≤ d)
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
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
    exists_sharp_projective_projection m n hmn I hI d hd hdim hdegree
  exact ⟨b, hint, hfield, f, hf,
    projection_equation_irreducible_map I _ f hf.ne_zero hker,
    hfhom, hfdeg, hker, hcount⟩

end
end AffineCurveCounting
