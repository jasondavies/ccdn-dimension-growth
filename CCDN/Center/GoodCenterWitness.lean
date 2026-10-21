/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Center.CenterMinorProjection
public import CCDN.Projection.ProjectionImageFractionField
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.CenterMinorMatrix
import CCDN.Center.FixedCoordinateCenterRows
import CCDN.Center.GeometricCenterRows
/-! Constructed good centers for the literal maximal-minor projection.
Equal kernels transfer both integrality and the generated function
field. The affine construction retains a zero first column. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_birational_minor_center
    {L : Type*} [Field L] [Algebra ℚ L] [Infinite L]
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) ℚ,
      LinearIndependent ℚ A.row ∧
      (∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap ℚ L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap ℚ L)).row)) ∧
      (projectionCoordinateMap I (centerMinorProjectionForm A)).IsIntegral ∧
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
        I (centerMinorProjectionForm A) = ⊤ := by
  obtain ⟨b, A, hA, hker, hdisjoint, hint, hfield⟩ :=
    exists_geometric_center_row_witness (L := L) m n hmn I hI d hdimdeg
  have hr : n - m - 1 + 2 ≤ n + 1 := by omega
  let B : Matrix (Fin (m + 2)) (Fin (n + 1)) ℚ := fun i j => (b i j : ℚ)
  have hforms : chowProjectionForms B = fun i => integerLinearForm (b i) := rfl
  refine ⟨A, hA, hdisjoint, ?_, ?_⟩
  · exact centerMinorProjectionForm_isIntegral_of_ker I A hA hr B hker.le (hforms.symm ▸ hint)
  · rw [projectionImageField_centerMinorProjectionForm_of_ker I A hA hr B hker.symm, hforms]
    exact hfield

/-- Every affine prime source has a constructed finite birational center
for its projective closure lying in X0=0. This includes dimension zero.
The projection is the literal maximal-minor projection. -/
theorem exists_fixed_coordinate_birational_minor_center
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [Infinite L]
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) K,
      LinearIndependent K A.row ∧ (∀ i, A i 0 = 0) ∧
      (∀ p ∈ projectiveIdealZeroLocus ((projectiveClosureIdeal I).map (map (algebraMap K L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap K L)).row)) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (centerMinorProjectionForm A)).IsIntegral ∧
      projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I) (centerMinorProjectionForm A) = ⊤ := by
  obtain ⟨B, A, _, hA, hA0, hker, hdisjoint, hint, hfield⟩ :=
    exists_fixed_coordinate_center_row_witness (L := L) I hmn d hdimdeg
  have hr : n - m - 1 + 2 ≤ n + 1 := by omega
  refine ⟨A, hA, hA0, hdisjoint,
    centerMinorProjectionForm_isIntegral_of_ker _ A hA hr B hker.le hint, ?_⟩
  rw [projectionImageField_centerMinorProjectionForm_of_ker _ A hA hr B hker.symm]
  exact hfield

end
end CCDN
