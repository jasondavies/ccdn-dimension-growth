module

public import CCDN.ProjectiveDimensionGrowth
public import CCDN.ProjectiveHilbertCurveGrowth
public import CCDN.ProperHilbertDimension
public import CCDN.PolynomialPredicates

/-! A cubic degree exponent for general projective dimension growth.
This is an independent consequence of the constructed projections and the
plane curve estimate. The original paper's numerical exponent remark is
among the statements amended in the author's corrigendum. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma projectiveProjectionDegreeExponent_le_cubic {m k n : ℕ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (h : m + k + 1 = n) :
    projectiveProjectionDegreeExponent m k ≤ 2 * n ^ 3 := by
  have hm : m + 2 ≤ n := by omega
  have hp := Nat.mul_le_mul_left (2 * (n + 1)) (show m + 1 ≤ n - 1 by omega)
  have hl := Nat.mul_le_mul_left 9 hm
  have he : m + k + 2 = n + 1 := by omega
  have hpred : n - 1 + 1 = n := by omega
  have hquad : projectiveProjectionDegreeExponent m k + 1 ≤ 2 * n ^ 2 + 10 * n := by
    dsimp only [projectiveProjectionDegreeExponent]
    rw [he]
    nlinarith
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  rw [ht] at hquad ⊢
  nlinarith

theorem projective_variety_dimension_growth_cubic_indices (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m k : ℕ, m + k + 1 = n → 1 ≤ k →
      ∀ I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).natDegree = m + 2 →
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 2).factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) * B ^ (m + 1) := by
  classical
  choose C hC hcount using projective_variety_dimension_growth
  let T : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), C i j
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), C i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le))
  refine ⟨T, by dsimp only [T]; linarith, ?_⟩
  intro m k hmk hkpos I hprime hI d hd hdim hdegree B hB
  have hm : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hk : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hsmall : C m k ≤ T := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (n + 1)) => (hC m j).le) hk
    have hj : (∑ j ∈ Finset.range (n + 1), C m j) ≤
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), C i j :=
      Finset.single_le_sum
      (fun i (_ : i ∈ Finset.range (n + 1)) =>
        Finset.sum_nonneg (fun j _ => (hC i j).le)) hm
    dsimp only [T]
    linarith
  have hpow : (d : ℝ) ^ projectiveProjectionDegreeExponent m k ≤
      (d : ℝ) ^ (2 * n ^ 3) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d by omega))
      (projectiveProjectionDegreeExponent_le_cubic hn hkpos hmk)
  apply (hcount m k I hprime hI d hd hdim hdegree B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hsmall hpow (by positivity) (by dsimp only [T]; linarith))
    (by positivity)

theorem projective_variety_dimension_growth_cubic_positive (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      2 ≤ (filteredHilbertPolynomial I).natDegree →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) := by
  by_cases hn2 : n = 2
  · subst n
    obtain ⟨C, hC, hcount⟩ := projective_hilbert_curve_dimension_growth 2 (by omega)
    refine ⟨C, hC, ?_⟩
    intro I hprime hI hdim d hd hdegree B hB
    have hdimlt := hilbert_dimension_lt_ambient_of_degree_gt_one I hprime.ne_top d
      (by omega) hdegree
    simp only [Fintype.card_fin] at hdimlt
    have hdim2 : (filteredHilbertPolynomial I).natDegree = 2 := by omega
    have hh := hcount I hprime hI d hd hdim2 (by simpa [hdim2] using hdegree) B hB
    rw [hdim2]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, pow_one]
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d by omega)) (by omega)) hC.le)
      (by positivity)
  have hn3 : 3 ≤ n := by omega
  obtain ⟨C, hC, hcount⟩ := projective_variety_dimension_growth_cubic_indices n hn3
  refine ⟨C, hC, ?_⟩
  intro I hprime hI hdim d hd hdegree B hB
  have hdimlt := hilbert_dimension_lt_ambient_of_degree_gt_one I hprime.ne_top d
    (by omega) hdegree
  simp only [Fintype.card_fin] at hdimlt
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hdim
  have hm' : (filteredHilbertPolynomial I).natDegree = m + 2 := by omega
  have hmn : m + 1 ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  have hkpos : 1 ≤ k := by omega
  have he : n = m + k + 1 := by omega
  clear hk
  subst n
  have hh := hcount m k rfl hkpos I hprime hI d hd hm'
    (by simpa only [hm'] using hdegree) B hB
  simpa only [hm', show m + 2 - 1 = m + 1 by omega] using hh

/-- Theorem 1 admits the explicit exponent `2*n^3` in every ambient
projective dimension, including the zero-dimensional and empty cases.
No projection, fiber bound or geometric auxiliary is assumed. -/
theorem projective_dimension_growth_cubic (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) := by
  have hpositive : ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      2 ≤ (filteredHilbertPolynomial I).natDegree →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) := by
    by_cases hn : 2 ≤ n
    · exact projective_variety_dimension_growth_cubic_positive n hn
    refine ⟨1, by norm_num, ?_⟩
    intro I hprime _ hdim d hd hdegree B _
    have hh := hilbert_dimension_lt_ambient_of_degree_gt_one I hprime.ne_top d
      (by omega) hdegree
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨C, hC, hcount⟩ := hpositive
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro I hprime hI d hd hdegree B hB
  let : I.IsPrime := hprime
  by_cases hdim0 : (filteredHilbertPolynomial I).natDegree = 0
  · rw [projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero I hdim0]
    have hz : projectiveCount (∅ : Set (ProjectivePoint n)) B = 0 := by
      simp [projectiveCount, projectivePoints]
    rw [hz, Nat.cast_zero]
    positivity
  by_cases hdim1 : (filteredHilbertPolynomial I).natDegree = 1
  · have hbound := zero_dimensional_projective_count_le I d hdim1 (by
      simpa only [hdim1, Nat.factorial_one, Nat.cast_one, div_one] using hdegree) B
    have hdimlt := hilbert_dimension_lt_ambient_of_degree_gt_one I hprime.ne_top d
      (by omega) hdegree
    simp only [Fintype.card_fin, hdim1] at hdimlt
    have hn : 1 ≤ n := by omega
    have hpower : n + 1 ≤ 2 * n ^ 3 := by
      have h1 : n ≤ n ^ 2 := by nlinarith
      have h2 := Nat.mul_le_mul_left n h1
      nlinarith
    have hpow : (d : ℝ) ^ (n + 1) ≤ (d : ℝ) ^ (2 * n ^ 3) :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d by omega)) hpower
    rw [hdim1, Nat.sub_self, pow_zero, mul_one]
    exact (Nat.cast_le.mpr hbound).trans (by
      rw [Nat.cast_pow]
      exact hpow.trans (le_mul_of_one_le_left (by positivity) (le_max_right C 1)))
  apply (hcount I hprime hI (by omega) d hd hdegree B hB).trans
  gcongr
  exact le_max_left C 1

end
end CCDN
