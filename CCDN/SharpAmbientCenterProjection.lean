module

public import CCDN.SharpGoodCenterProjection
public import CCDN.PolynomialPredicates

/-! The full ambient height quantifier of CCDN Lemma 5.1. The constructed
finite birational complementary projection has the required height bound
at every rational point outside its center, not just on the source. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma birational_complement_projection_ambient_height
    {n m r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [J.IsPrime]
    (M : Matrix (Fin r) (Fin (n + 1)) ℤ) (D : ℤ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hdata : BirationalComplementProjection J M D P)
    (hP : ∀ i j, |P i j| ≤ 2 * (sharpCenterMinorBound r m d : ℤ))
    (hrn : r ≤ n + 1) (hmn : m + 1 ≤ n + 1) (hd : 1 ≤ d)
    (x : ProjectivePoint n)
    (hx : x.rep ∉ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row)) :
    ∃ hnon : normalizedIntegerProjection D P x.rep ≠ 0,
      (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hnon).mulHeight ≤
        (centerProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * r ^ 2) * x.mulHeight := by
  have hnon : normalizedIntegerProjection D P x.rep ≠ 0 := by
    intro hz
    apply hx
    rw [← hdata.kernel, LinearMap.mem_ker]
    exact hz
  refine ⟨hnon, ?_⟩
  have hb : ∀ i j, |(P i j : ℝ)| ≤ 2 * (sharpCenterMinorBound r m d : ℝ) := by
    intro i j
    exact_mod_cast hP i j
  apply (normalizedIntegerProjection_projective_height D hdata.scale_ne_zero P
    (by positivity) hb x hnon).trans
  apply mul_le_mul_of_nonneg_right _ x.mulHeight_pos.le
  have hh := center_projection_source_exponent_all_rows (m := m) (n := n)
    (r := r) (d := d) hrn hmn hd
  exact_mod_cast (show (n + 1) * (2 * sharpCenterMinorBound r m d) ≤
      centerProjectionHeightConstant n * d ^ (2 * r ^ 2) from by
    simpa only [sharpCenterMinorBound, mul_assoc] using hh)

/-- Lemma 5.1, with the literal ambient height
quantifier and an explicit dimension-only constant. Geometric integrality
and degree preservation of the projection image are included. -/
theorem exists_sharp_ambient_birational_projection
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    ∃ (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ x ∈ projectiveIdealZeroLocus (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))),
        x.rep ∉ Submodule.span (AlgebraicClosure ℚ)
          (Set.range ((M.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).row)) ∧
      BirationalComplementProjection J M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 ∧
      ∀ x : ProjectivePoint (n + 1),
        x.rep ∉ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) →
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (centerProjectionHeightConstant (n + 1) : ℝ) *
              (d : ℝ) ^ (2 * (n + 1 - m - 1) ^ 2) * x.mulHeight := by
  obtain ⟨s,e,M,hM,_,hli,hc,hint,hf⟩ :=
    exists_sharp_bounded_integer_birational_center hmn J hJ d hdim hdegree
  obtain ⟨D,P,hdata,hP,hdim',_⟩ :=
    exists_bounded_birational_complement_of_minor_projection J hJ M hli
      ((m + 1) ^ 2 * d ^ 2)
      (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2) e hint hf
  have hdim'' : Module.finrank ℚ (normalizedIntegerProjection D P).range +
      (n + 1 - m - 1) = n + 2 := hdim'
  have hdimension : Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 := by
    omega
  refine ⟨M,D,P,hM,hli,hc,hdata,hdimension,?_⟩
  apply birational_complement_projection_ambient_height (n := n + 1) (m := m) (d := d)
    J M D P hdata
    (fun i j => ?_) (by omega) (by omega) (hilbert_multiplicity_pos_of_prime J hdegree)
  simpa only [sharpCenterMinorBound, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hP i j

/-- The fixed-coordinate form retains the ambient height bound, including
zero-dimensional sources and the empty-center case. -/
theorem exists_sharp_ambient_fixed_coordinate_projection
    {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ (M : Matrix (Fin (n + 1 - m - 1)) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, 0 ≤ M i j ∧ M i j ≤ ((m + 1) ^ 2 * d ^ 2)) ∧ (∀ i, M i 0 = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      (∀ x ∈ projectiveIdealZeroLocus
          ((projectiveClosureIdeal I).map (map (algebraMap ℚ (AlgebraicClosure ℚ)))),
        x.rep ∉ Submodule.span (AlgebraicClosure ℚ)
          (Set.range ((M.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).row)) ∧
      BirationalComplementProjection (projectiveClosureIdeal I) M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 ∧
      ∀ x : ProjectivePoint (n + 1),
        x.rep ∉ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) →
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (centerProjectionHeightConstant (n + 1) : ℝ) *
              (d : ℝ) ^ (2 * (n + 1 - m - 1) ^ 2) * x.mulHeight := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I
  obtain ⟨s,e,M,hM,_,hM0,hli,hc,hint,hf⟩ :=
    exists_sharp_bounded_integer_fixed_coordinate_center I hmn d hdim hdegree
  obtain ⟨D,P,hdata,hP,hdim',_⟩ :=
    exists_bounded_birational_complement_of_minor_projection (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) M hli ((m + 1) ^ 2 * d ^ 2)
      (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2) e hint hf
  have hdim'' : Module.finrank ℚ (normalizedIntegerProjection D P).range +
      (n + 1 - m - 1) = n + 2 := hdim'
  have hdimension : Module.finrank ℚ (normalizedIntegerProjection D P).range = m + 2 := by
    omega
  refine ⟨M,D,P,hM,hM0,hli,hc,hdata,hdimension,?_⟩
  apply birational_complement_projection_ambient_height (n := n + 1) (m := m) (d := d)
    (projectiveClosureIdeal I) M D P hdata
    (fun i j => ?_) (by omega) (by omega) (hilbert_multiplicity_pos_of_prime I hdegree)
  simpa only [sharpCenterMinorBound, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hP i j

end
end CCDN
