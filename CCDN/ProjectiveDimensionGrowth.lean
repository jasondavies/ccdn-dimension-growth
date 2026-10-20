module

public import CCDN.ProjectiveVarietyUniformGrowth
public import CCDN.ZeroDimensionalProjectiveCount
public import CCDN.EmptyProjectiveHilbertDimension
public import CCDN.PolynomialPredicates

/-! CCDN Theorem 1 in the homogeneous-coordinate-ideal formulation:
uniform projective dimension growth for every rational prime projective
variety of degree at least five. The Hilbert polynomial determines
the degree and dimension. All projections, fibers and counting inputs are
proved internally, including zero-dimensional and empty loci. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Uniform dimension growth in every projective dimension. The constant
and the explicit polynomial degree exponent depend only on the ambient
projective space. Rational irreducibility suffices. -/
theorem projective_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ ambientProjectiveDegreeExponent n *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_variety_dimension_growth_uniform n
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro I hprime hI d hd hdegree B hB
  let : I.IsPrime := hprime
  by_cases hdim0 : (filteredHilbertPolynomial I).natDegree = 0
  · rw [projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero I hdim0]
    have hzero : projectiveCount (∅ : Set (ProjectivePoint n)) B = 0 := by
      simp [projectiveCount, projectivePoints]
    rw [hzero, Nat.cast_zero]
    positivity
  by_cases hdim1 : (filteredHilbertPolynomial I).natDegree = 1
  · have hbound := zero_dimensional_projective_count_le I d hdim1 (by
      simpa only [hdim1, Nat.factorial_one, Nat.cast_one, div_one] using hdegree) B
    have hpow : (d : ℝ) ^ (n + 1) ≤ (d : ℝ) ^ ambientProjectiveDegreeExponent n :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ d by omega))
        (by dsimp [ambientProjectiveDegreeExponent]; omega)
    rw [hdim1, Nat.sub_self, pow_zero, mul_one]
    exact (Nat.cast_le.mpr hbound).trans (by
      rw [Nat.cast_pow]
      exact hpow.trans (le_mul_of_one_le_left (by positivity) (le_max_right C 1)))
  have hdim : 2 ≤ (filteredHilbertPolynomial I).natDegree := by omega
  apply (hcount I hprime hI hdim d hd hdegree B hB).trans
  gcongr
  exact le_max_left C 1

end
end CCDN
