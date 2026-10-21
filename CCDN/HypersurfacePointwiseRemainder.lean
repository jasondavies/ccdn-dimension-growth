module

public import CCDN.PolynomialUniformDifference
public import CCDN.ActualLocalHilbertWeights

/-! The multiplicity-independent pointwise remainder of CCDN Lemma 2.1.
The leading coefficient is exact, and the error constant depends only on
the hypersurface dimension. Dimension one has no remainder at all. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Finset

/-- The integer polynomial n! * binomial(n+X,n). -/
def binomialNumeratorPolynomial (n : ℕ) : ℕ[X] :=
  (ascPochhammer ℕ n).comp (X + C 1)

lemma binomialNumeratorPolynomial_degree (n : ℕ) :
    (binomialNumeratorPolynomial n).natDegree = n := by
  simp [binomialNumeratorPolynomial, natDegree_comp, ascPochhammer_natDegree]

lemma binomialNumeratorPolynomial_monic (n : ℕ) :
    (binomialNumeratorPolynomial n).Monic :=
  (monic_ascPochhammer ℕ n).comp (monic_X_add_C 1) (by simp)

lemma binomialNumeratorPolynomial_eval (n k : ℕ) :
    (binomialNumeratorPolynomial n).eval k = n.factorial * (n + k).choose n := by
  rw [binomialNumeratorPolynomial, eval_comp]
  simp only [eval_add, eval_X, eval_C]
  rw [ascPochhammer_nat_eq_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose, Nat.add_comm k n]

/-- A dimension-only explicit constant for the pointwise error, in dimension n+2. -/
def hypersurfacePointwiseError (n : ℕ) : ℝ :=
  (polynomialDifferenceConstant (binomialNumeratorPolynomial (n + 2)) n : ℝ) /
    (n + 2).factorial

lemma hypersurfacePointwiseError_nonneg (n : ℕ) : 0 ≤ hypersurfacePointwiseError n := by
  unfold hypersurfacePointwiseError
  positivity

lemma hypersurfaceLayerBound_factorial_pointwise (n μ k : ℕ) (hk : 0 < k) :
    (n + 2).factorial * hypersurfaceLayerBound (n + 2) μ k ≤
      (n + 2) * μ * k ^ (n + 1) +
        polynomialDifferenceConstant (binomialNumeratorPolynomial (n + 2)) n * k ^ n := by
  by_cases hμ : μ ≤ k
  · have h := nat_polynomial_difference_uniform (binomialNumeratorPolynomial (n + 2)) n
      (binomialNumeratorPolynomial_degree _) (binomialNumeratorPolynomial_monic _) k μ hk hμ
    rw [binomialNumeratorPolynomial_eval, binomialNumeratorPolynomial_eval] at h
    rw [hypersurfaceLayerBound, ite_eq_left hμ, Nat.mul_sub_left_distrib]
    omega
  · have h := nat_polynomial_before_step_uniform (binomialNumeratorPolynomial (n + 2)) n
      (binomialNumeratorPolynomial_degree _) (binomialNumeratorPolynomial_monic _) k μ hk
      (by omega)
    rw [binomialNumeratorPolynomial_eval] at h
    simpa only [hypersurfaceLayerBound, ite_eq_right hμ, Nat.sub_zero] using h

/-- The exact printed pointwise estimate in every dimension at least two.
The same constant works for every multiplicity and every positive k. -/
theorem hypersurfaceLayerBound_pointwise_remainder (n μ k : ℕ) (hk : 0 < k) :
    (hypersurfaceLayerBound (n + 2) μ k : ℝ) ≤
      (μ : ℝ) * (k : ℝ) ^ (n + 1) / (n + 1).factorial +
        hypersurfacePointwiseError n * (k : ℝ) ^ n := by
  have h := hypersurfaceLayerBound_factorial_pointwise n μ k hk
  have hr : ((n + 2).factorial : ℝ) * hypersurfaceLayerBound (n + 2) μ k ≤
      (n + 2 : ℝ) * μ * (k : ℝ) ^ (n + 1) +
        polynomialDifferenceConstant (binomialNumeratorPolynomial (n + 2)) n * (k : ℝ) ^ n := by
    exact_mod_cast h
  have hf : (0 : ℝ) < (n + 2).factorial := by positivity
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ ≤ (n + 2 : ℝ) * μ * (k : ℝ) ^ (n + 1) +
        polynomialDifferenceConstant (binomialNumeratorPolynomial (n + 2)) n * (k : ℝ) ^ n := hr
    _ = _ := by
      unfold hypersurfacePointwiseError
      have hf₁ : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      have hf₂ : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
      have he : ((n + 2).factorial : ℝ) = (n + 2 : ℝ) * (n + 1).factorial := by
        exact_mod_cast Nat.factorial_succ (n + 1)
      field_simp
      rw [he]
      ring

/-- In dimension one, the printed estimate holds with error zero. -/
theorem hypersurfaceLayerBound_dimension_one_le (μ k : ℕ) :
    hypersurfaceLayerBound 1 μ k ≤ μ := by
  simpa using hypersurfaceLayerBound_le_mul_choose 0 μ k

/-- Uniform pointwise error in every positive dimension, using the literal
real exponent m-2. The dimension-one error constant is zero. -/
theorem exists_hypersurfaceLayerBound_uniform_error (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ k : ℕ, 0 < k →
      (hypersurfaceLayerBound m μ k : ℝ) ≤
        (μ : ℝ) * (k : ℝ) ^ (m - 1) / (m - 1).factorial +
          C * (k : ℝ) ^ ((m : ℝ) - 2) := by
  by_cases hm1 : m = 1
  · subst m
    refine ⟨0, le_rfl, ?_⟩
    intro μ k _
    simpa using (show (hypersurfaceLayerBound 1 μ k : ℝ) ≤ μ from
      Nat.cast_le.mpr (hypersurfaceLayerBound_dimension_one_le μ k))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
    refine ⟨hypersurfacePointwiseError n, hypersurfacePointwiseError_nonneg n, ?_⟩
    intro μ k hk
    have he : ((n + 2 : ℕ) : ℝ) - 2 = (n : ℝ) := by push_cast; ring
    rw [show n + 2 - 1 = n + 1 by omega, he, Real.rpow_natCast]
    exact hypersurfaceLayerBound_pointwise_remainder n μ k hk

/-- A single constant, chosen before the field, equation and rational point,
gives the exact Lemma 2.1 remainder for every hypersurface stalk of
positive dimension. -/
theorem exists_hypersurfacePointStalk_pointwise_remainder (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : Type*) [Field K] (f : MvPolynomial (Fin (m + 1)) K)
        (a : Fin (m + 1) → K) [Fact (MvPolynomial.eval a f = 0)], f ≠ 0 →
        ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
          (∀ k, hypersurfacePointLayerDimension f a k = hypersurfaceLayerBound m μ k) ∧
          ∀ k : ℕ, 0 < k → (hypersurfacePointLayerDimension f a k : ℝ) ≤
            (μ : ℝ) * (k : ℝ) ^ (m - 1) / (m - 1).factorial +
              C * (k : ℝ) ^ ((m : ℝ) - 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_hypersurfaceLayerBound_uniform_error m hm
  refine ⟨C, hC, ?_⟩
  intro K _ f a _ hf
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨μ, hpos, hdeg, hprofile, _⟩ :=
    exists_hypersurfacePointStalk_hilbert_weights f a hf
  refine ⟨μ, hpos, hdeg, hprofile, ?_⟩
  intro k hk
  rw [hprofile]
  exact hbound μ k hk

end
end CCDN
