module

public import AffineCurveCounting.PrimeIdealGridBound
public import AffineCurveCounting.PureComponentDegreeBudget

/-! The exact pure-dimensional grid bound of CCDN Lemma 4.1.1.
The actual minimal-prime components cover every point. Their constructed
Hilbert multiplicities satisfy the additive degree budget, and the sharp
prime grid bound applies to each component. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- A zero of an ideal belongs to one of its actual minimal-prime components,
over an arbitrary coefficient field. -/
theorem exists_minimalPrimeComponent_vanishing
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (x : σ → K)
    (hx : ∀ f ∈ I, eval x f = 0) :
    ∃ P : minimalPrimeComponents I, ∀ f ∈ P.val, eval x f = 0 := by
  classical
  let J := RingHom.ker (eval x)
  let : J.IsPrime := RingHom.ker_isPrime (eval x)
  have hIJ : I ≤ J := fun f hf => hx f hf
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le hIJ
  exact ⟨⟨P, mem_minimalPrimeComponents.mpr hP⟩, fun f hf => hPJ hf⟩

/-- A pure-dimensional affine ideal of multiplicity d has at most d*|S|^m
points in the finite coordinate grid S. No component family is supplied. -/
theorem pure_ideal_grid_card_le
    {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (m d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d * S.card ^ m := by
  classical
  by_cases hI : I = ⊤
  · have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := hzero x hx 1 (by simp [hI])
      simp only [map_one, one_ne_zero] at hh
    simp [hs]
  obtain ⟨δ, hδ, hbudget⟩ :=
    exists_minimalPrimeComponents_multiplicity_budget I hI m d hdim hdegree hpure
  let t (P : minimalPrimeComponents I) := s.filter (fun x => ∀ f ∈ P.val, eval x f = 0)
  have ht (P : minimalPrimeComponents I) : (t P).card ≤ δ P * S.card ^ m := by
    let : P.val.IsPrime := minimalPrimeComponents_isPrime P.property
    have hh := prime_ideal_grid_card_le n P.val (δ P)
      (by simpa only [hpure P] using (hδ P).2) S (t P)
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => hgrid x (Finset.mem_filter.mp hx).1)
    simpa only [hpure P] using hh
  have hcover : s ⊆ Finset.univ.biUnion t := by
    intro x hx
    obtain ⟨P, hP⟩ := exists_minimalPrimeComponent_vanishing I x (hzero x hx)
    exact Finset.mem_biUnion.mpr ⟨P, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hP⟩⟩
  calc
    s.card ≤ (Finset.univ.biUnion t).card := Finset.card_le_card hcover
    _ ≤ ∑ P, (t P).card := Finset.card_biUnion_le
    _ ≤ ∑ P, δ P * S.card ^ m := Finset.sum_le_sum (fun P _ => ht P)
    _ = (∑ P, δ P) * S.card ^ m := (Finset.sum_mul ..).symm
    _ ≤ d * S.card ^ m := Nat.mul_le_mul_right _ hbudget

/-- The integer interval form of the pure-dimensional rational variety bound. -/
theorem pure_variety_count_le_integer_interval
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (m d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m) (B : ℝ) :
    count (idealZeroLocus I) B ≤ d * ((2 * ⌊B⌋ + 1).toNat) ^ m := by
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
  have hh := pure_ideal_grid_card_le n I m d hdim hdegree hpure T (S.image rationalPoint)
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

/-- CCDN Lemma 4.1.1, with the exact constant and box side: the number of
integer points on a pure-dimensional affine variety is at most d(2B+1)^m. -/
theorem pure_variety_count_le_degree_mul_box_side
    {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (m d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I) B : ℝ) ≤ (d : ℝ) * (2 * B + 1) ^ m := by
  have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hside : ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤ 2 * B + 1 := by
    have he : (((2 * ⌊B⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ 2 * ⌊B⌋ + 1 by omega))
    rw [he]
    linarith [Int.floor_le B]
  calc
    _ ≤ (d : ℝ) * ((2 * ⌊B⌋ + 1).toNat : ℝ) ^ m := by
      exact_mod_cast pure_variety_count_le_integer_interval I m d hdim hdegree hpure B
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hside m) (Nat.cast_nonneg _)

end
end AffineCurveCounting
