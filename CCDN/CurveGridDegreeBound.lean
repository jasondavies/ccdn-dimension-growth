module

public import CCDN.HilbertCoordinateIndependence
public import CCDN.PolynomialSection
public import CCDN.SmallOutsidePoint

/-! The sharp degree-times-grid-side bound for prime curves in arbitrary
affine dimension. The coordinate and all section bounds are constructed
from the actual filtered Hilbert polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem filtered_hilbert_dimension_one_eventually_linear
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ M ≥ N,
      (Module.finrank K (filteredCoordinateSpace I M) : ℤ) = (d : ℤ) * M + c := by
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  have hc : (filteredHilbertPolynomial I).coeff 1 = (d : ℚ) := by
    simpa only [Polynomial.leadingCoeff, hdim] using hdegree
  have hP := Polynomial.eq_X_add_C_of_natDegree_le_one hdim.le
  rw [hc] at hP
  refine ⟨N, (Module.finrank K (filteredCoordinateSpace I N) : ℤ) - d * N, ?_⟩
  intro M hM
  have h₀ := hN N le_rfl
  have h₁ := hN M hM
  rw [hP] at h₀ h₁
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h₀ h₁
  have he : (Module.finrank K (filteredCoordinateSpace I M) : ℚ) =
      (d : ℚ) * M + ((Module.finrank K (filteredCoordinateSpace I N) : ℚ) - d * N) := by
    linarith
  exact_mod_cast he

theorem exists_coordinate_all_linear_sections_proper
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤)
    (hdim : 0 < (filteredHilbertPolynomial I).natDegree) :
    ∃ j : σ, ∀ t : K, X j - C t ∉ I := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I hI
  have hnon : Nonempty U := by
    rw [Nat.card_eq_fintype_card] at hU
    exact Fintype.card_pos_iff.mp (by omega)
  let j : U := Classical.choice hnon
  refine ⟨j.val, fun t ht => ?_⟩
  have hzero : aeval (fun i : U => Ideal.Quotient.mk I (X i.val)) (X j - C t) = 0 := by
    simp only [map_sub, aeval_X, aeval_C]
    change Ideal.Quotient.mk I (X j.val) - Ideal.Quotient.mk I (C t) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  have he : (X j - C t : MvPolynomial U K) = 0 :=
    (algebraicIndependent_iff.mp hAI) _ hzero
  have hc := congrArg (fun p : MvPolynomial U K => p.coeff (Finsupp.single j 1)) he
  have hs : Finsupp.single j (1 : ℕ) ≠ 0 := by simp
  simp [Ne.symm hs] at hc

/-- The prime-curve case of CCDN Lemma 4.1.1, over any field and with any
finite coordinate grid. The slope is the actual Hilbert multiplicity. -/
theorem prime_curve_grid_card_le
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d)
    (S : Finset K) (s : Finset (σ → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) : s.card ≤ d * S.card := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_all_linear_sections_proper I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›) (by omega)
  have hlinear := filtered_hilbert_dimension_one_eventually_linear I d hdim hdegree
  apply Finset.card_le_mul_card_image_of_maps_to (fun x hx => hgrid x hx j) d
  intro t _
  let T := s.filter (fun x => x j = t)
  have hh := polynomial_section_card_le_degree I d hlinear
    (X j - C t) (hj t) 1
    ((totalDegree_sub _ _).trans (by simp))
    (fun x : T => x.val) Subtype.val_injective
    (fun x => hzero x.val (Finset.mem_filter.mp x.property).1)
    (by
      intro x
      simp only [map_sub, eval_X, eval_C, (Finset.mem_filter.mp x.property).2, sub_self])
  simpa only [Fintype.card_coe, Nat.mul_one] using hh

/-- For an actual rational prime curve in any ambient dimension, the
integer-point count is at most its degree times the integer interval size. -/
theorem prime_curve_count_le_degree_mul_integer_interval
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d) (B : ℝ) :
    count (idealZeroLocus I) B ≤ d * (2 * ⌊B⌋ + 1).toNat := by
  classical
  let S := integralPoints (idealZeroLocus I) B
  let T : Finset ℚ := (Finset.Icc (-⌊B⌋) ⌊B⌋).image (fun t : ℤ => (t : ℚ))
  have hcard : T.card = (2 * ⌊B⌋ + 1).toNat := by
    rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
    congr 1
    omega
  have hpoints : Function.Injective (rationalPoint : IntPoint n → RatPoint n) := by
    intro x y h
    funext i
    exact Int.cast_injective (congrFun h i)
  have hh := prime_curve_grid_card_le I d hdim hdegree T (S.image rationalPoint)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_integralPoints.mp ha).2)
    (by
      intro x hx i
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨a i, ?_, rfl⟩
      obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp ha).1 i)
      have hn : -(a i) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
      exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩)
  rw [Finset.card_image_of_injective _ hpoints, hcard] at hh
  exact hh

theorem prime_curve_count_le_degree_mul_box_side
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤ (d : ℝ) * (2 * B + 1) := by
  have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hside : ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤ 2 * B + 1 := by
    have he : (((2 * ⌊B⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ 2 * ⌊B⌋ + 1 by omega))
    rw [he]
    linarith [Int.floor_le B]
  calc
    _ ≤ (d : ℝ) * ((2 * ⌊B⌋ + 1).toNat : ℝ) := by
      exact_mod_cast prime_curve_count_le_degree_mul_integer_interval I d hdim hdegree B
    _ ≤ _ := mul_le_mul_of_nonneg_left hside (Nat.cast_nonneg _)

end
end CCDN
