module

public import CCDN.SharpBirationalCenterNonvanishing
public import CCDN.SharpCenterBounds
public import CCDN.ZeroColumnMinorSpecialization
public import CCDN.PolynomialPredicates

/-! Integer good centers with the quadratic row bound from the
row-resultant detector. Dimension zero is included using its proved degree
one. Prescribed zero columns of a witness center are preserved, which gives
centers in X0=0 for affine sources. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

def sharpCenterMinorBound (r m d : ℕ) : ℕ := r.factorial * ((m + 1) ^ 2 * d ^ 2) ^ r

/-- A good center with zero columns `S` yields a good center with bounded
nonnegative integer entries and the same zero columns. -/
theorem exists_sharp_bounded_integer_center_of_witness
    {n m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (S : Finset (Fin (n + 2))) (A : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℚ)
    (hA : LinearIndependent ℚ A.row) (hAS : ∀ i j, j ∈ S → A i j = 0)
    (hgood : IsBirationalMatrixCenter J A) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ sharpCenterMinorBound (n + 1 - m - 1) m d) ∧
      (∀ i j, j ∈ S → M i j = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter J (M.map (Int.castRingHom ℚ)) := by
  obtain ⟨G,hhom,hdeg,hvalue,hgoodG⟩ :=
    exists_nonzero_sharp_center_detector J hJ d hdim hdegree (by omega) A hA hgood
  have hG : G ≠ 0 := by intro hz; simp [hz] at hvalue
  have hhom' : G.IsHomogeneous G.totalDegree := (hhom.totalDegree hG) ▸ hhom
  obtain ⟨M,hM,hM0,hli,hv,hminor⟩ :=
    exists_sharp_integer_minor_specialization_zero_columns S G hhom' A hA hAS hvalue
  have hbound : max 1 G.totalDegree ≤ ((m + 1) ^ 2 * d ^ 2) :=
    (max_le_max_left 1 hdeg).trans (sharp_center_detector_degree_le_square
      (hilbert_multiplicity_pos_of_prime J hdegree)
      (geometric_projective_multiplicity_boundary J hJ hdim hdegree))
  have hb : ((max 1 G.totalDegree : ℕ) : ℤ) ≤ ((m + 1) ^ 2 * d ^ 2) := by exact_mod_cast hbound
  refine ⟨M,fun i j => ⟨(hM i j).1,(hM i j).2.trans hb⟩,fun c => ?_,hM0,hli,hgoodG _ hli hv⟩
  apply (hminor c).trans
  simp only [sharpCenterMinorBound, Nat.cast_mul, Nat.cast_pow]
  gcongr
  exact_mod_cast hbound

/-- The geometric good center has bounded integer independent rows. -/
theorem exists_sharp_bounded_integer_birational_center
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ sharpCenterMinorBound (n + 1 - m - 1) m d) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter J (M.map (Int.castRingHom ℚ)) := by
  obtain ⟨A,hA,hdis,_,hfield⟩ :=
    exists_birational_minor_center (L := AlgebraicClosure ℚ) m (n + 1) hmn J hJ d hdim hdegree
  obtain ⟨M,hM,hminor,_,hli,hgood⟩ := exists_sharp_bounded_integer_center_of_witness J hJ d
    hdim hdegree ∅ A hA (fun _ _ h => absurd h (Finset.notMem_empty _)) ⟨hdis,hfield⟩
  exact ⟨M,hM,hminor,hli,hgood⟩

/-- The same construction inside X0=0, for the projective closure of an
affine source. -/
theorem exists_sharp_bounded_integer_fixed_coordinate_center
    {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ,
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ sharpCenterMinorBound (n + 1 - m - 1) m d) ∧
      (∀ i, M i 0 = 0) ∧ LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      IsBirationalMatrixCenter (projectiveClosureIdeal I) (M.map (Int.castRingHom ℚ)) := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I
  obtain ⟨hcdim, hcdeg⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  obtain ⟨A,hA,hA0,hdis,_,hfield⟩ :=
    exists_fixed_coordinate_birational_minor_center (L := AlgebraicClosure ℚ) I hmn d hdim hdegree
  obtain ⟨M,hM,hminor,hM0,hli,hgood⟩ := exists_sharp_bounded_integer_center_of_witness
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I) d hcdim hcdeg {0} A hA
    (fun i j hj => by simpa only [Finset.mem_singleton.mp hj] using hA0 i) ⟨hdis,hfield⟩
  exact ⟨M,hM,hminor,fun i => hM0 i 0 (Finset.mem_singleton_self 0),hli,hgood⟩

end
end CCDN
