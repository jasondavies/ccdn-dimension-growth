module

public import CCDN.SharpBirationalCenterDetector
public import CCDN.BirationalMinorCenterWitness
public import CCDN.ProjectiveClosureHilbertPolynomial
public import CCDN.PolynomialPredicates

/-! Nonzero sharp resultant detector polynomials with constructed rational
witnesses. The fixed-coordinate version constructs its witness inside the
subspace of centers contained in X0=0, including affine dimension zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_nonzero_sharp_birational_center_detector
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (G : MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) ℚ)
      (A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℚ),
      G.IsHomogeneous (((m + 1) * d) * (2 * d - 1)) ∧
      G.totalDegree ≤ ((m + 1) * d) * (2 * d - 1) ∧
      LinearIndependent ℚ A.row ∧
      eval (fun c : Fin (n + 1 - m - 1) ↪ Fin (n + 2) => (A.submatrix id c).det) G ≠ 0 ∧
      ∀ (B : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℚ), LinearIndependent ℚ B.row →
        eval (fun c : Fin (n + 1 - m - 1) ↪ Fin (n + 2) => (B.submatrix id c).det) G ≠ 0 →
        (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))),
          p.rep ∉ Submodule.span (AlgebraicClosure ℚ)
            (Set.range (B.map (algebraMap ℚ (AlgebraicClosure ℚ))).row)) ∧
        projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) ℚ ⧸ J))
          J (chowProjectionForms (centerMinorProjectionMatrix B e)) = ⊤ := by
  obtain ⟨s, e, Φ, hhom, hdeg, hΦ⟩ := exists_sharp_birational_center_detector J hJ d hdim hdegree
    (show n + 1 - m - 1 + 2 ≤ n + 2 by omega)
  obtain ⟨A, t, e', hA, hc, _, hf⟩ :=
    exists_birational_minor_center (L := AlgebraicClosure ℚ) m (n + 1) hmn J hJ d hdim hdegree
  have hker : (centerMinorProjectionMatrix A e).mulVecLin.ker =
      (centerMinorProjectionMatrix A e').mulVecLin.ker := by
    rw [centerMinorProjectionMatrix_ker A hA e, centerMinorProjectionMatrix_ker A hA e']
  have hf' : projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) ℚ ⧸ J))
      J (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
    rw [projectionImageField_eq_of_matrix_kernel_eq J _ _ hker]
    exact hf
  obtain ⟨G, hG, heval⟩ := (hΦ A hA).mpr ⟨hc, hf'⟩
  refine ⟨s, e, G, A, hhom G hG, hdeg G hG, hA, heval, ?_⟩
  intro B hB hGB
  exact (hΦ B hB).mp ⟨G, hG, hGB⟩

/-- The chosen detector remains nonzero after restricting to center
matrices whose first column is zero. The witness is constructed from the
affine ideal. -/
theorem exists_nonzero_sharp_fixed_coordinate_center_detector
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (G : MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) K)
      (A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) K),
      G.IsHomogeneous (((m + 1) * d) * (2 * d - 1)) ∧
      G.totalDegree ≤ ((m + 1) * d) * (2 * d - 1) ∧
      LinearIndependent K A.row ∧ (∀ i, A i 0 = 0) ∧
      eval (fun c : Fin (n + 1 - m - 1) ↪ Fin (n + 2) => (A.submatrix id c).det) G ≠ 0 ∧
      ∀ (B : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) K), LinearIndependent K B.row →
        eval (fun c : Fin (n + 1 - m - 1) ↪ Fin (n + 2) => (B.submatrix id c).det) G ≠ 0 →
        (∀ p ∈ projectiveIdealZeroLocus
            ((projectiveClosureIdeal I).map (map (algebraMap K (AlgebraicClosure K)))),
          p.rep ∉ Submodule.span (AlgebraicClosure K)
            (Set.range (B.map (algebraMap K (AlgebraicClosure K))).row)) ∧
        projectionImageField
          (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ projectiveClosureIdeal I))
          (projectiveClosureIdeal I) (chowProjectionForms (centerMinorProjectionMatrix B e)) = ⊤ := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure K) I
  obtain ⟨hcdim, hcdeg⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  obtain ⟨s, e, Φ, hhom, hdeg, hΦ⟩ := exists_sharp_birational_center_detector (projectiveClosureIdeal I)
    (projectiveClosureIdeal_homogeneous I) d hcdim hcdeg
    (show n + 1 - m - 1 + 2 ≤ n + 2 by omega)
  obtain ⟨A, t, e', hA, hA0, hc, _, hf⟩ :=
    exists_fixed_coordinate_birational_minor_center (L := AlgebraicClosure K) I hmn d hdim hdegree
  have hker : (centerMinorProjectionMatrix A e).mulVecLin.ker =
      (centerMinorProjectionMatrix A e').mulVecLin.ker := by
    rw [centerMinorProjectionMatrix_ker A hA e, centerMinorProjectionMatrix_ker A hA e']
  have hf' : projectionImageField
      (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ projectiveClosureIdeal I))
      (projectiveClosureIdeal I) (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
    rw [projectionImageField_eq_of_matrix_kernel_eq _ _ _ hker]
    exact hf
  obtain ⟨G, hG, heval⟩ := (hΦ A hA).mpr ⟨hc, hf'⟩
  refine ⟨s, e, G, A, hhom G hG, hdeg G hG, hA, hA0, heval, ?_⟩
  intro B hB hGB
  exact (hΦ B hB).mp ⟨G, hG, hGB⟩

end
end CCDN
