module

public import CCDN.BirationalCenterNonvanishing
public import CCDN.ZeroColumnMinorSpecialization

/-! Bounded integer good centers from the constructed Chow--Noether
condition. The cubic detector bound is used explicitly; this is distinct
from the sharper quadratic estimate printed in Section 5. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

def cubicCenterRowBound (m d : ℕ) : ℕ := (max 1 ((m + 1) * d)) ^ 3

def cubicCenterMinorBound (r m d : ℕ) : ℕ := r.factorial * cubicCenterRowBound m d ^ r

lemma center_detector_degree_le_cubic (D : ℕ) :
    max 1 (D * max 1 (D ^ 2 - 1)) ≤ (max 1 D) ^ 3 := by
  have h1 : 1 ≤ max 1 D := le_max_left _ _
  have hD : D ≤ max 1 D := le_max_right _ _
  have h2 : max 1 (D ^ 2 - 1) ≤ (max 1 D) ^ 2 :=
    max_le (one_le_pow₀ h1) ((Nat.sub_le _ _).trans (Nat.pow_le_pow_left hD 2))
  apply max_le (one_le_pow₀ h1)
  calc
    D * max 1 (D ^ 2 - 1) ≤ max 1 D * (max 1 D) ^ 2 := Nat.mul_le_mul hD h2
    _ = (max 1 D) ^ 3 := by ring

/-- The actual geometric good center has bounded integer independent rows.
Both integrality and birationality concern its literal minor projection. -/
theorem exists_bounded_integer_birational_center
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ cubicCenterRowBound m d) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ cubicCenterMinorBound (n + 1 - m - 1) m d) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))),
        p.rep ∉ Submodule.span (AlgebraicClosure ℚ)
          (Set.range ((M.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).row)) ∧
      (projectionCoordinateMap J (chowProjectionForms
        (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e))).IsIntegral ∧
      projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) ℚ ⧸ J)) J
        (chowProjectionForms (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e)) = ⊤ := by
  obtain ⟨s,e,G,A,hhom,hdeg,hA,hvalue,hgood⟩ :=
    exists_nonzero_birational_center_detector hmn J hJ d hdim hdegree
  have hG : G ≠ 0 := by intro hz; simp [hz] at hvalue
  have hhom' : G.IsHomogeneous G.totalDegree := (hhom.totalDegree hG) ▸ hhom
  obtain ⟨M,hM,hli,hv,hminor⟩ := exists_sharp_integer_minor_specialization G hhom' A hA hvalue
  have hbound : max 1 G.totalDegree ≤ cubicCenterRowBound m d :=
    (max_le_max_left 1 hdeg).trans (center_detector_degree_le_cubic ((m + 1) * d))
  have hb : ((max 1 G.totalDegree : ℕ) : ℤ) ≤ cubicCenterRowBound m d := by exact_mod_cast hbound
  obtain ⟨hc,hf⟩ := hgood _ hli hv
  have hliL := linearIndependent_matrix_rows_map (algebraMap ℚ (AlgebraicClosure ℚ)) _ hli
  have hc' := centerMinorProjectionMatrix_disjoint _ _ hliL e hc
  have hint := projection_integral_of_geometric_center_disjoint (L := AlgebraicClosure ℚ) J hJ
    (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e)
    (by rwa [centerMinorProjectionMatrix_map])
  refine ⟨s,e,M,fun i j => ⟨(hM i j).1,(hM i j).2.trans hb⟩,?_,hli,hc,hint,hf⟩
  intro c
  apply (hminor c).trans
  simp only [cubicCenterMinorBound, Nat.cast_mul, Nat.cast_pow]
  gcongr

/-- The same construction inside X0=0. The original affine variety and
its projective closure supply all geometric hypotheses internally. -/
theorem exists_bounded_integer_fixed_coordinate_center
    {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ cubicCenterRowBound m d) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ cubicCenterMinorBound (n + 1 - m - 1) m d) ∧
      (∀ i, M i 0 = 0) ∧ LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ p ∈ projectiveIdealZeroLocus
          ((projectiveClosureIdeal I).map (map (algebraMap ℚ (AlgebraicClosure ℚ)))),
        p.rep ∉ Submodule.span (AlgebraicClosure ℚ)
          (Set.range ((M.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).row)) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I) (chowProjectionForms
        (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e))).IsIntegral ∧
      projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 2)) ℚ ⧸ projectiveClosureIdeal I))
        (projectiveClosureIdeal I)
        (chowProjectionForms (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e)) = ⊤ := by
  classical
  obtain ⟨s,e,G,A,hhom,hdeg,hA,hA0,hvalue,hgood⟩ :=
    exists_nonzero_fixed_coordinate_center_detector I hmn d hdim hdegree
  have hG : G ≠ 0 := by intro hz; simp [hz] at hvalue
  have hhom' : G.IsHomogeneous G.totalDegree := (hhom.totalDegree hG) ▸ hhom
  obtain ⟨M,hM,hM0,hli,hv,hminor⟩ :=
    exists_sharp_integer_minor_specialization_zero_columns {0} G hhom' A hA
      (by intro i j hj; simpa only [Finset.mem_singleton.mp hj] using hA0 i) hvalue
  have hbound : max 1 G.totalDegree ≤ cubicCenterRowBound m d :=
    (max_le_max_left 1 hdeg).trans (center_detector_degree_le_cubic ((m + 1) * d))
  have hb : ((max 1 G.totalDegree : ℕ) : ℤ) ≤ cubicCenterRowBound m d := by exact_mod_cast hbound
  obtain ⟨hc,hf⟩ := hgood _ hli hv
  have hliL := linearIndependent_matrix_rows_map (algebraMap ℚ (AlgebraicClosure ℚ)) _ hli
  have hc' := centerMinorProjectionMatrix_disjoint _ _ hliL e hc
  have hint := projection_integral_of_geometric_center_disjoint (L := AlgebraicClosure ℚ) (projectiveClosureIdeal I)
    (projectiveClosureIdeal_homogeneous I)
    (centerMinorProjectionMatrix (M.map (Int.castRingHom ℚ)) e)
    (by rwa [centerMinorProjectionMatrix_map])
  refine ⟨s,e,M,fun i j => ⟨(hM i j).1,(hM i j).2.trans hb⟩,?_,
    fun i => hM0 i 0 (Finset.mem_singleton_self 0),hli,hc,hint,hf⟩
  intro c
  apply (hminor c).trans
  simp only [cubicCenterMinorBound, Nat.cast_mul, Nat.cast_pow]
  gcongr

end
end CCDN
