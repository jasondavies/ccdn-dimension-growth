module

public import CCDN.TopFormSurfaceCount
public import CCDN.BoundedHyperplaneDimensionGrowth
public import CCDN.PolynomialPredicates

/-! Large-degree affine dimension growth in every ambient dimension at
least three. The surface estimate supplies degree exponent eighteen;
each bounded hyperplane slicing step adds nine. The hyperplane, its
integer level equations, and their point maps are all constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem top_form_hypersurface_count_large_degree_add (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (3 + n)) ℤ,
      HasAbsIrreducibleTopForm f →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  exact top_form_hypersurface_count_of_surface_bound 16 18 (by norm_num)
    top_form_surface_count n

/-- Theorem 4's affine dimension-growth form for every degree at least
sixteen, with an explicit polynomial degree exponent. The constant
depends only on the number of variables, before the equation or radius
is chosen. No auxiliary, slice, geometric-family, or counting premise
is supplied by the caller. -/
theorem top_form_hypersurface_count_large_degree (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      HasAbsIrreducibleTopForm f →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  rw [show n + 3 = 3 + n by omega]
  exact top_form_hypersurface_count_large_degree_add n

end
end CCDN
