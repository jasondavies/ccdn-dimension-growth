module

public import CCDN.SharpCenterExtensionDetector
public import CCDN.BirationalMinorCenterWitness
public import CCDN.PolynomialPredicates

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

theorem exists_birational_center_matrix_over_extension
    {L : Type*} [Field L] [Algebra ℚ L] {n m s : ℕ}
    (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    [(J.map (map (algebraMap ℚ L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    ∃ A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) L,
      LinearIndependent L A.row ∧ IsBirationalMatrixCenter (J.map (map (algebraMap ℚ L))) e A := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let E := AlgebraicClosure L
  have hJE : (J.map (map (algebraMap ℚ E))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  obtain ⟨A,t,e',hA,hdis,hint,hfield⟩ :=
    exists_birational_minor_center (L := E) m (n + 1) hmn J hJ d hdim hdegree
  let AL := A.map (algebraMap ℚ L)
  let JL := J.map (map (algebraMap ℚ L))
  have hAL : LinearIndependent L AL.row := linearIndependent_matrix_rows_map _ A hA
  have hdisL : ∀ p ∈ projectiveIdealZeroLocus (JL.map (map (algebraMap L E))),
      p.rep ∉ Submodule.span E (Set.range (AL.map (algebraMap L E)).row) := by
    dsimp only [JL,AL]
    rw [ideal_scalar_extension_tower,matrix_map_algebraMap_tower]
    exact hdis
  have hker : (centerMinorProjectionMatrix A e).mulVecLin.ker =
      (centerMinorProjectionMatrix A e').mulVecLin.ker := by
    rw [centerMinorProjectionMatrix_ker A hA e,centerMinorProjectionMatrix_ker A hA e']
  have hint' : (projectionCoordinateMap J (chowProjectionForms (centerMinorProjectionMatrix A e))).IsIntegral :=
    projection_integral_of_matrix_kernel_le J _ _ hker.le hint
  have hfield' : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) ℚ ⧸ J)) J
      (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
    rw [projectionImageField_eq_of_matrix_kernel_eq J _ _ hker]
    exact hfield
  have hgeom := centerMinorProjectionMatrix_disjoint
    (JL.map (map (algebraMap L E))) (AL.map (algebraMap L E))
    (linearIndependent_matrix_rows_map _ AL hAL) e hdisL
  have hintL : (projectionCoordinateMap JL
      (chowProjectionForms (centerMinorProjectionMatrix AL e))).IsIntegral := by
    apply projection_integral_of_geometric_center_disjoint (L := E) JL
      (homogeneous_ideal_scalar_extension (L := L) J hJ)
    rw [centerMinorProjectionMatrix_map]
    exact hgeom
  refine ⟨AL,hAL,hdisL,?_⟩
  have hh := homogeneous_matrix_projection_birational_scalar_extension J hJ
    (centerMinorProjectionMatrix A e) hint'
    (by simpa only [centerMinorProjectionMatrix_map] using hintL) hfield'
  simpa only [centerMinorProjectionMatrix_map] using hh

end
end CCDN
