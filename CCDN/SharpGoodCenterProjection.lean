module

public import CCDN.SharpBoundedBirationalCenter
public import CCDN.BirationalComplementProjection

/-! Unconditional bounded complementary projections at the height exponent
of CCDN Section 5.1. The row-resultant detector constructs quadratic bounded
integer center rows; the actual image is geometrically integral with the
same degree. Centers in X0=0 and the dimension-zero boundary are included. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Construct the actual complementary projection from a projective
geometrically integral source. The degree loss in height is 2r², where r is
the vector dimension of the center, as in the source statement. -/
theorem exists_sharp_bounded_birational_projective_projection
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ sharpCenterMinorBound (n + 1 - m - 1) m d) ∧
      BirationalComplementProjection J M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 ∧
      (∀ i j, |P i j| ≤ 2 * (sharpCenterMinorBound (n + 1 - m - 1) m d : ℤ)) ∧
      ∀ x ∈ projectiveIdealZeroLocus J,
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (centerProjectionHeightConstant (n + 1) : ℝ) *
              (d : ℝ) ^ (2 * (n + 1 - m - 1) ^ 2) * x.mulHeight := by
  obtain ⟨s,e,M,hM,hminor,hli,_,hint,hfield⟩ :=
    exists_sharp_bounded_integer_birational_center hmn J hJ d hdim hdegree
  obtain ⟨D,P,hdata,hP,hPdim,hheight⟩ :=
    exists_bounded_birational_complement_of_minor_projection J hJ M hli
      (((m + 1) ^ 2 * d ^ 2)) (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2)
      e hint hfield
  have hPdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range +
      (n + 1 - m - 1) = n + 2 := hPdim
  have hdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 := by omega
  refine ⟨M,D,P,hM,hli,hminor,hdata,hdim',?_,?_⟩
  · intro i j
    simpa only [sharpCenterMinorBound, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hP i j
  intro x hx
  obtain ⟨hnon,hh⟩ := hheight x hx
  refine ⟨hnon,hh.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ x.mulHeight_pos.le
  exact_mod_cast center_projection_source_exponent_all_rows (n := n + 1)
    (r := n + 1 - m - 1) (m := m) (d := d) (by omega) (by omega)
    (hilbert_multiplicity_pos_of_prime J hdegree)

/-- A bounded good center contained in X0=0 and the genuine complementary
projection of the actual projective closure of an affine source. This also
covers dimension zero and the zero-row (empty-center) boundary. -/
theorem exists_sharp_bounded_fixed_coordinate_projection
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧ (∀ i, M i 0 = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ c : Fin (n + 1 - m - 1) ↪ Fin (n + 2),
        |(M.submatrix id c).det| ≤ sharpCenterMinorBound (n + 1 - m - 1) m d) ∧
      BirationalComplementProjection (projectiveClosureIdeal I) M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 ∧
      (∀ i j, |P i j| ≤ 2 * (sharpCenterMinorBound (n + 1 - m - 1) m d : ℤ)) ∧
      ∀ x ∈ projectiveIdealZeroLocus (projectiveClosureIdeal I),
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (centerProjectionHeightConstant (n + 1) : ℝ) *
              (d : ℝ) ^ (2 * (n + 1 - m - 1) ^ 2) * x.mulHeight := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I
  obtain ⟨s,e,M,hM,hminor,hM0,hli,_,hint,hfield⟩ :=
    exists_sharp_bounded_integer_fixed_coordinate_center I hmn d hdim hdegree
  obtain ⟨D,P,hdata,hP,hPdim,hheight⟩ :=
    exists_bounded_birational_complement_of_minor_projection (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) M hli (((m + 1) ^ 2 * d ^ 2))
      (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2) e hint hfield
  have hPdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range +
      (n + 1 - m - 1) = n + 2 := hPdim
  have hdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 := by omega
  refine ⟨M,D,P,hM,hM0,hli,hminor,hdata,hdim',?_,?_⟩
  · intro i j
    simpa only [sharpCenterMinorBound, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hP i j
  intro x hx
  obtain ⟨hnon,hh⟩ := hheight x hx
  refine ⟨hnon,hh.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ x.mulHeight_pos.le
  exact_mod_cast center_projection_source_exponent_all_rows (n := n + 1)
    (r := n + 1 - m - 1) (m := m) (d := d) (by omega) (by omega)
    (hilbert_multiplicity_pos_of_prime I hdegree)

end
end CCDN
