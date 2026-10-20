module

public import AffineCurveCounting.ProjectiveVarietyDimensionGrowth

/-! Constants uniform in the ambient projective space. A finite maximum
over dimensions and codimensions removes all dependence on the variety. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def ambientProjectiveDegreeExponent (n : ℕ) : ℕ :=
  18 + 10 * (n + 1) + 2 * (n + 1) ^ 2

lemma projectiveProjectionDegreeExponent_le_ambient {m k n : ℕ}
    (h : m + k + 1 = n) :
    projectiveProjectionDegreeExponent m k ≤ ambientProjectiveDegreeExponent n := by
  have hmn : m ≤ n + 1 := by omega
  have hmn' : m + 1 ≤ n + 1 := by omega
  have hprod := Nat.mul_le_mul_left (2 * (n + 1)) hmn'
  have hlin := Nat.mul_le_mul_left 9 hmn
  dsimp only [projectiveProjectionDegreeExponent, ambientProjectiveDegreeExponent]
  have he : m + k + 2 = n + 1 := by omega
  rw [he]
  nlinarith

theorem projective_variety_dimension_growth_uniform_indices (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m k : ℕ, m + k + 1 = n →
      ∀ I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ), I.IsPrime →
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).natDegree = m + 2 →
      (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 2).factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ ambientProjectiveDegreeExponent n * B ^ (m + 1) := by
  classical
  choose C hC hcount using projective_variety_dimension_growth
  let T : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), C i j
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), C i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le))
  refine ⟨T, by dsimp only [T]; linarith, ?_⟩
  intro m k hmk I hprime hI d hd hdim hdegree B hB
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
      (d : ℝ) ^ ambientProjectiveDegreeExponent n :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d by omega))
      (projectiveProjectionDegreeExponent_le_ambient hmk)
  apply (hcount m k I hprime hI d hd hdim hdegree B hB).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hsmall hpow (by positivity) (by dsimp only [T]; linarith))
    (by positivity)

/-- General positive-dimensional projective varieties of degree at least
five, with a single constant and a single degree exponent for each ambient
projective space. The height exponent is the actual projective dimension. -/
theorem projective_variety_dimension_growth_uniform (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      (∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) →
      2 ≤ (filteredHilbertPolynomial I).natDegree →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ ambientProjectiveDegreeExponent n *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_variety_dimension_growth_uniform_indices n
  refine ⟨C, hC, ?_⟩
  intro I hprime hI hdim d hd hdegree B hB
  have hdimle : (filteredHilbertPolynomial I).natDegree ≤ n + 1 := by
    obtain ⟨_, _, hh, _⟩ := filteredHilbertPolynomial_positive_multiplicity I hprime.ne_top
    simpa only [Fintype.card_fin] using hh
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hdim
  have hm' : (filteredHilbertPolynomial I).natDegree = m + 2 := by omega
  have hmn : m + 1 ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  have hn : n = m + k + 1 := by omega
  clear hk
  subst n
  have hh := hcount m k rfl I hprime hI d hd hm' (by simpa only [hm'] using hdegree) B hB
  simpa only [hm', show m + 2 - 1 = m + 1 by omega] using hh

end
end AffineCurveCounting
