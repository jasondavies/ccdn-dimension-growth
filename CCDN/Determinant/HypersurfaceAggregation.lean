module

public import CCDN.Determinant.HypersurfaceMultiplicityEstimate
/-! Sharp aggregation of local hypersurface exponents. Summing the exact
integer cutoff inequalities before optimizing preserves the leading constant
and gives a linear error independent of all residue multiplicities. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A common cutoff aggregates without any loss in the leading coefficient. -/
theorem aggregate_hypersurface_exponents_cutoff {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (s μ : ι → ℕ) (hμ : ∀ i, 0 < μ i) (K : ℕ) :
    (∑ i, s i) * K ≤ (∑ i, hypersurfaceMultiplicityExponent m (μ i) (s i)) +
      (∑ i, μ i) * (m + K).choose (m + 1) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hypersurfaceMultiplicityExponent_cutoff_pos m (s i) K hm (hμ i))
  simpa only [Finset.sum_add_distrib, ← Finset.sum_mul] using h

/-- The sharp leading term depends only on the sum of local multiplicities,
with exactly the same dimension-only error as the single-residue bound. -/
theorem aggregate_hypersurface_exponents_sharp {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (s μ : ι → ℕ) (hμ : ∀ i, 0 < μ i)
    (hμsum : 0 < ∑ i, μ i) :
    ((m.factorial : ℝ) / (∑ i, μ i : ℕ)) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (∑ i, s i : ℕ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * (∑ i, s i : ℕ) ≤
        (∑ i, hypersurfaceMultiplicityExponent m (μ i) (s i) : ℕ) :=
  local_exponent_sharp m (∑ i, s i) _ hm hμsum
    (aggregate_hypersurface_exponents_cutoff m hm s μ hμ)

end
end CCDN
