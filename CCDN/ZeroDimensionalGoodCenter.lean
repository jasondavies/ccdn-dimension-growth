module

public import CCDN.CubicGoodCenterProjection
public import CCDN.ZeroDimensionalGeometricPoint
public import CCDN.PolynomialPredicates

/-! The degree-one boundary of the bounded-center construction. A
geometrically integral zero-dimensional projective source has degree one.
The constructed centers then have only zero and one entries, without a
quadratic bad-center polynomial or a supplied rational point. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem geometric_projective_dimension_zero_multiplicity_one
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ)) : d = 1 := by
  classical
  obtain ⟨j,hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J (by omega)
  let e := Equiv.swap 0 j
  let J' := projectivePermutedIdeal J e
  let : J'.IsPrime := projectivePermutedIdeal_isPrime J e
  let : (J'.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime J e
  have hJ' := projectivePermutedIdeal_homogeneous J hJ e
  have hX : X 0 ∉ J' := by
    change X 0 ∉ projectivePermutedIdeal J e
    rw [mem_projectivePermutedIdeal,rename_X]
    simpa only [e,Equiv.swap_apply_left] using hj
  have hp := projectivePermutedIdeal_filteredHilbertPolynomial J e
  have hdim' : (filteredHilbertPolynomial J').natDegree = 0 + 1 :=
    (congrArg Polynomial.natDegree hp).trans hdim
  have hd' : (filteredHilbertPolynomial J').leadingCoeff = (d : ℚ) / (0 + 1).factorial := by
    simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, div_one] using
      (congrArg Polynomial.leadingCoeff hp).trans hdegree
  obtain ⟨hmI,hdI⟩ := projectiveChartIdeal_hilbertPolynomial_parameters J' hJ' hX 0 d hdim' hd'
  let : ((projectiveChartIdeal J').map (map (algebraMap K (AlgebraicClosure K)))).IsPrime :=
    projectiveChartIdeal_geometrically_prime J' hX
  obtain ⟨_,_,hpoly⟩ := zero_dimensional_geometrically_integral_point
    (L := AlgebraicClosure K) (projectiveChartIdeal J') hmI
  have hq : (1 : ℚ) = d := by
    simpa only [hpoly,Polynomial.leadingCoeff_one,Nat.factorial_zero,Nat.cast_one,div_one] using hdI
  exact_mod_cast hq.symm

/-- The geometric projective point has an actual bounded good center whose
entries are zero or one, and a complementary projection of the same degree.
The height constant depends only on the ambient dimension. -/
theorem exists_zero_dimensional_zero_one_center_projection
    {n : ℕ} (hn : 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = 1) :
    ∃ (M : Matrix (Fin n) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      BirationalComplementProjection J M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = 2 ∧
      (∀ i j, |P i j| ≤ 2 * (n.factorial : ℤ)) ∧
      ∀ x ∈ projectiveIdealZeroLocus J,
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (n + 2 : ℕ) * (2 * (n.factorial : ℝ)) * x.mulHeight := by
  obtain ⟨d,_,_,hd⟩ := filteredHilbertPolynomial_positive_multiplicity J
    (Ideal.IsPrime.ne_top ‹J.IsPrime›)
  have hd' : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) := by
    simpa only [hdim,Nat.factorial_one,Nat.cast_one,div_one] using hd
  have he := geometric_projective_dimension_zero_multiplicity_one J hJ d hdim hd'
  subst d
  obtain ⟨s,e,M,hM,_,hli,_,hint,hfield⟩ :=
    exists_bounded_integer_birational_center (m := 0) hn J hJ 1 hdim
      (by simpa only [Nat.zero_add,Nat.factorial_one,Nat.cast_one,div_one] using hd')
  have hM' : ∀ i j, 0 ≤ M i j ∧ M i j ≤ 1 := by
    simpa only [cubicCenterRowBound,Nat.zero_add,mul_one,max_self,one_pow,Nat.cast_one] using hM
  obtain ⟨D,P,hdata,hP,hPdim,hheight⟩ :=
    exists_bounded_birational_complement_of_minor_projection J hJ M hli 1
      (fun i j => by rw [abs_of_nonneg (hM' i j).1]; exact (hM' i j).2) e hint hfield
  have hdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range = 2 := by
    have hh : Module.finrank ℚ (normalizedIntegerProjection D P).range + n = n + 2 := by
      simpa only [Nat.sub_zero,Nat.add_sub_cancel] using hPdim
    omega
  refine ⟨M,D,P,fun i j => by have := hM' i j; omega,hli,hdata,hdim',?_,?_⟩
  · simpa only [Nat.sub_zero,Nat.add_sub_cancel,Nat.cast_one,one_pow,mul_one] using hP
  · simpa only [Nat.sub_zero,Nat.add_sub_cancel,Nat.cast_one,one_pow,mul_one] using hheight

/-- The zero-dimensional affine boundary has a good zero-one center in
X0=0, including the empty-center case. -/
theorem exists_zero_dimensional_fixed_zero_one_center_projection
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    ∃ (M : Matrix (Fin n) (Fin (n + 2)) ℤ) (D : ℤ)
      (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ),
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧ (∀ i, M i 0 = 0) ∧
      LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row ∧
      BirationalComplementProjection (projectiveClosureIdeal I) M D P ∧
      Module.finrank ℚ (normalizedIntegerProjection D P).range = 2 ∧
      (∀ i j, |P i j| ≤ 2 * (n.factorial : ℤ)) ∧
      ∀ x ∈ projectiveIdealZeroLocus (projectiveClosureIdeal I),
        ∃ hx : normalizedIntegerProjection D P x.rep ≠ 0,
          (Projectivization.mk ℚ (normalizedIntegerProjection D P x.rep) hx).mulHeight ≤
            (n + 2 : ℕ) * (2 * (n.factorial : ℝ)) * x.mulHeight := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I
  obtain ⟨_,_,hpoly⟩ := zero_dimensional_geometrically_integral_point (L := AlgebraicClosure ℚ) I hdim
  have hd : (filteredHilbertPolynomial I).leadingCoeff = (1 : ℚ) / (0 : ℕ).factorial := by
    simp only [hpoly,Polynomial.leadingCoeff_one,Nat.factorial_zero,Nat.cast_one,div_one]
  obtain ⟨s,e,M,hM,_,hM0,hli,_,hint,hfield⟩ :=
    exists_bounded_integer_fixed_coordinate_center (m := 0) I (by omega) 1 hdim hd
  have hM' : ∀ i j, 0 ≤ M i j ∧ M i j ≤ 1 := by
    simpa only [cubicCenterRowBound,Nat.zero_add,mul_one,max_self,one_pow,Nat.cast_one] using hM
  obtain ⟨D,P,hdata,hP,hPdim,hheight⟩ :=
    exists_bounded_birational_complement_of_minor_projection (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) M hli 1
      (fun i j => by rw [abs_of_nonneg (hM' i j).1]; exact (hM' i j).2) e hint hfield
  have hdim' : Module.finrank ℚ (normalizedIntegerProjection D P).range = 2 := by
    have hh : Module.finrank ℚ (normalizedIntegerProjection D P).range + n = n + 2 := by
      simpa only [Nat.sub_zero,Nat.add_sub_cancel] using hPdim
    omega
  refine ⟨M,D,P,fun i j => by have := hM' i j; omega,hM0,hli,hdata,hdim',?_,?_⟩
  · simpa only [Nat.sub_zero,Nat.add_sub_cancel,Nat.cast_one,one_pow,mul_one] using hP
  · simpa only [Nat.sub_zero,Nat.add_sub_cancel,Nat.cast_one,one_pow,mul_one] using hheight

end
end CCDN
