module

public import AffineCurveCounting.GeometricCenterRows
public import AffineCurveCounting.FixedCoordinateCenterRows
public import AffineCurveCounting.MatrixProjectionFields

/-! Constructed good centers for the literal maximal-minor projection.
Equal kernels transfer both integrality and the actual generated function
field. The affine construction retains a zero first column. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

theorem exists_birational_minor_center
    {L : Type*} [Field L] [Algebra ℚ L] [Infinite L]
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ (A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) ℚ) (s : ℕ)
      (e : Fin (s + 2) ≃ (Fin (n - m - 1 + 1) ↪ Fin (n + 1))),
      LinearIndependent ℚ A.row ∧
      (∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap ℚ L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap ℚ L)).row)) ∧
      (projectionCoordinateMap I (chowProjectionForms (centerMinorProjectionMatrix A e))).IsIntegral ∧
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
        I (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
  obtain ⟨b, A, hA, hker, hdisjoint, hint, hfield⟩ :=
    exists_geometric_center_row_witness (L := L) m n hmn I hI d hdim hdegree
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration
    (show n - m - 1 + 2 ≤ n + 1 by omega)
  let B : Matrix (Fin (m + 2)) (Fin (n + 1)) ℚ := fun i j => (b i j : ℚ)
  have hforms : chowProjectionForms B = fun i => integerLinearForm (b i) := rfl
  have hMker : (centerMinorProjectionMatrix A e).mulVecLin.ker = B.mulVecLin.ker :=
    (centerMinorProjectionMatrix_ker A hA e).trans hker
  refine ⟨A, s, e, hA, hdisjoint, ?_, ?_⟩
  · exact projection_integral_of_matrix_kernel_le I _ B hMker.le (hforms.symm ▸ hint)
  · rw [projectionImageField_eq_of_matrix_kernel_eq I _ B hMker, hforms]
    exact hfield

/-- Every affine prime source has a constructed finite birational center
for its actual projective closure lying in X0=0. This includes dimension zero.
The result is a literal minor projection, with no supplied center witness. -/
theorem exists_fixed_coordinate_birational_minor_center
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [Infinite L]
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hmn : m + 1 ≤ n) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ (A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) K) (s : ℕ)
      (e : Fin (s + 2) ≃ (Fin (n - m - 1 + 1) ↪ Fin (n + 1))),
      LinearIndependent K A.row ∧ (∀ i, A i 0 = 0) ∧
      (∀ p ∈ projectiveIdealZeroLocus ((projectiveClosureIdeal I).map (map (algebraMap K L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap K L)).row)) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (chowProjectionForms (centerMinorProjectionMatrix A e))).IsIntegral ∧
      projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I) (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
  obtain ⟨B, A, _, hA, hA0, hker, hdisjoint, hint, hfield⟩ :=
    exists_fixed_coordinate_center_row_witness (L := L) I hmn d hdim hdegree
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration
    (show n - m - 1 + 2 ≤ n + 1 by omega)
  have hMker : (centerMinorProjectionMatrix A e).mulVecLin.ker = B.mulVecLin.ker :=
    (centerMinorProjectionMatrix_ker A hA e).trans hker
  refine ⟨A, s, e, hA, hA0, hdisjoint,
    projection_integral_of_matrix_kernel_le _ _ B hMker.le hint, ?_⟩
  rw [projectionImageField_eq_of_matrix_kernel_eq _ _ B hMker]
  exact hfield

end
end AffineCurveCounting
