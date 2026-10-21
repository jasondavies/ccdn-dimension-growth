/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.CenterDetectorExtension
public import CCDN.Center.GoodCenterWitness
public import CCDN.Algebra.PolynomialPredicates
/-! Constructed rational centers remain geometrically disjoint
birational centers after arbitrary extension of the coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma homogeneous_matrix_projection_birational_scalar_extension
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hint : (projectionCoordinateMap J (chowProjectionForms A)).IsIntegral)
    (hintL : (projectionCoordinateMap (J.map (map (algebraMap K L)))
      (chowProjectionForms (A.map (algebraMap K L)))).IsIntegral)
    (hf : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J))
      J (chowProjectionForms A) = ⊤) :
    projectionImageField
      (F := FractionRing (MvPolynomial (Fin (n + 1)) L ⧸ J.map (map (algebraMap K L))))
      (J.map (map (algebraMap K L))) (chowProjectionForms (A.map (algebraMap K L))) = ⊤ := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have he := (homogeneous_finite_projection_leadingCoeff_eq_iff_birational
    (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J hJ
    (chowProjectionForms A) (chowProjectionForms_homogeneous A) hint).mpr hf
  apply homogeneous_finite_projection_birational_of_leadingCoeff_eq _
    (homogeneous_ideal_scalar_extension (L := L) J hJ) _
    (chowProjectionForms_homogeneous _) hintL
  change (filteredHilbertPolynomial (chowProjectionImageIdeal
    (J.map (map (algebraMap K L))) (A.map (algebraMap K L)))).leadingCoeff = _
  rw [chowProjectionImageIdeal_hilbertPolynomial_scalar_extension,
    filteredHilbertPolynomial_scalar_extension]
  exact he

lemma matrix_map_algebraMap_tower
    {K L E : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    {α β : Type*} (A : Matrix α β K) :
    (A.map (algebraMap K L)).map (algebraMap L E) = A.map (algebraMap K E) := by
  ext i j
  exact (IsScalarTower.algebraMap_apply K L E (A i j)).symm

/-- A finite birational center over K remains a geometrically disjoint
birational center after extending the coefficients to any field L. -/
theorem isBirationalMatrixCenter_map_of_finite_birational
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J) (hr : r + 2 ≤ n + 1)
    (A : Matrix (Fin r) (Fin (n + 1)) K) (hA : LinearIndependent K A.row)
    (hdis : ∀ p ∈ projectiveIdealZeroLocus
        ((J.map (map (algebraMap K L))).map (map (algebraMap L (AlgebraicClosure L)))),
      p.rep ∉ Submodule.span (AlgebraicClosure L)
        (Set.range ((A.map (algebraMap K L)).map (algebraMap L (AlgebraicClosure L))).row))
    (hint : (projectionCoordinateMap J (centerMinorProjectionForm A)).IsIntegral)
    (hfield : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
      (centerMinorProjectionForm A) = ⊤) :
    IsBirationalMatrixCenter (J.map (map (algebraMap K L))) (A.map (algebraMap K L)) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  let E := AlgebraicClosure L
  let AL := A.map (algebraMap K L)
  let JL := J.map (map (algebraMap K L))
  have hAL : LinearIndependent L AL.row := linearIndependent_matrix_rows_map _ A hA
  have hint' := (centerMinorProjectionMatrix_isIntegral_iff J A e).mpr hint
  have hfield' : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J)) J
      (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
    rw [projectionImageField_centerMinorProjectionMatrix]
    exact hfield
  have hgeom := centerMinorProjectionMatrix_disjoint
    (JL.map (map (algebraMap L E))) (AL.map (algebraMap L E))
    (linearIndependent_matrix_rows_map _ AL hAL) e hdis
  have hintL : (projectionCoordinateMap JL
      (chowProjectionForms (centerMinorProjectionMatrix AL e))).IsIntegral := by
    apply projection_integral_of_geometric_center_disjoint (L := E) JL
      (homogeneous_ideal_scalar_extension (L := L) J hJ)
    rw [centerMinorProjectionMatrix_map]
    exact hgeom
  refine ⟨hdis,?_⟩
  have hh := homogeneous_matrix_projection_birational_scalar_extension J hJ
    (centerMinorProjectionMatrix A e) hint'
    (by simpa only [centerMinorProjectionMatrix_map] using hintL) hfield'
  rw [← projectionImageField_centerMinorProjectionMatrix _ AL e]
  simpa only [centerMinorProjectionMatrix_map] using hh

theorem exists_birational_center_matrix_over_extension
    {L : Type*} [Field L] [Algebra ℚ L] {n m : ℕ}
    (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    [(J.map (map (algebraMap ℚ L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) L,
      LinearIndependent L A.row ∧ IsBirationalMatrixCenter (J.map (map (algebraMap ℚ L))) A := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hJE : (J.map (map (algebraMap ℚ (AlgebraicClosure L)))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  obtain ⟨A,hA,hdis,hint,hfield⟩ :=
    exists_birational_minor_center (L := AlgebraicClosure L) m (n + 1) hmn J hJ d hdimdeg
  refine ⟨_,linearIndependent_matrix_rows_map _ A hA,
    isBirationalMatrixCenter_map_of_finite_birational J hJ (by omega) A hA ?_ hint hfield⟩
  rw [ideal_scalar_extension_tower,matrix_map_algebraMap_tower]
  exact hdis

/-- The fixed-coordinate witness: a center in X0=0 for the projective closure
of an affine source, good over every extension field. -/
theorem exists_fixed_coordinate_birational_center_matrix_over_extension
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [((projectiveClosureIdeal I).map (map (algebraMap K L))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) L,
      LinearIndependent L A.row ∧ (∀ i, A i 0 = 0) ∧
      IsBirationalMatrixCenter ((projectiveClosureIdeal I).map (map (algebraMap K L))) A := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨A,hA,hA0,hdis,hint,hfield⟩ :=
    exists_fixed_coordinate_birational_minor_center (L := AlgebraicClosure L) I hmn d hdim hdegree
  refine ⟨_,linearIndependent_matrix_rows_map _ A hA,fun i => ?_,
    isBirationalMatrixCenter_map_of_finite_birational _ (projectiveClosureIdeal_homogeneous I)
      (by omega) A hA ?_ hint hfield⟩
  · simp only [Matrix.map_apply,hA0,map_zero]
  · rw [ideal_scalar_extension_tower,matrix_map_algebraMap_tower]
    exact hdis

end
end CCDN
