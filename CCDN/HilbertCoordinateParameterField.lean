module

public import CCDN.HilbertCoordinateIndependence
public import CCDN.HilbertFunctionFieldRank
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Construct a finite linear parameter field from coordinate
functions, in arbitrary Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def coordinateParameterField {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [Algebra (MvPolynomial σ K ⧸ I) F]
    (U : Set σ) : IntermediateField K F :=
  IntermediateField.adjoin K (Set.range (fun i : U =>
    algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (X i.val))))

/-- There is a subset of coordinate functions whose generated field
has finite extension degree at most the Hilbert multiplicity.
No parameter field, normalization or finiteness premise is supplied. -/
theorem exists_finite_coordinate_parameter_field
    {K F σ : Type*} [Field K] [Field F] [Fintype σ] [LinearOrder σ] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      AlgebraicIndependent K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) ∧
      Module.Finite (coordinateParameterField (F := F) I U) F ∧
      Module.finrank (coordinateParameterField (F := F) I U) F ≤ d := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  refine ⟨U, hU, hAI, ?_⟩
  let R := coordinateParameterField (F := F) I U
  let φ := IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F
  let u : U → R := fun i => ⟨φ ((Ideal.Quotient.mk I) (X i.val)),
    IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have huF : AlgebraicIndependent K
      (fun i : U => φ ((Ideal.Quotient.mk I) (X i.val))) :=
    hAI.map' (IsFractionRing.injective _ _)
  have hu : AlgebraicIndependent K u := by
    apply AlgebraicIndependent.of_comp R.val
    exact huF
  have hdim : (filteredHilbertPolynomial I).natDegree = Fintype.card U := by
    simpa only [Nat.card_eq_fintype_card] using hU.symm
  exact hilbert_functionField_finite_rank_le I d hdim (by simpa only [← hdim] using hdegree)
    (fun i : U => X i.val) (fun _ => by simp) u hu (fun _ => rfl)

end
end CCDN
