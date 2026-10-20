module

public import CCDN.CubicHyperplaneDimensionGrowth
public import CCDN.TopFormDimensionGrowthAllDegrees
public import CCDN.PolynomialPredicates

/-! The corrected affine degree exponent in CCDN Remark 4.3.8.
In N=n+3 variables the exponent is 18+3n=3N+9, using the corrected
surface bound d^18 and the cubic good-hyperplane bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN Theorem 4 for integer equations in all affine ambient dimensions
at least three. The constant depends only on dimension, and the explicit
degree exponent is 18 + 3n in n+3 variables. -/
theorem top_form_hypersurface_dimension_growth_cubic (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  rw [show n + 3 = 3 + n by omega]
  exact top_form_hypersurface_count_cubic_of_surface_bound 5 18 (by norm_num)
    top_form_surface_dimension_growth n


/-- The rational-equation version of the full affine bound. -/
theorem rational_top_form_hypersurface_dimension_growth_cubic (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := top_form_hypersurface_dimension_growth_cubic n
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB
  obtain ⟨g, hdeg, htop, hzero⟩ := exists_integer_model_absolute_top f hir
  have hpoints : integralPoints (zeroLocus (map (Int.castRingHom ℚ) g)) B =
      integralPoints (zeroLocus f) B := by
    ext x
    simp only [mem_integralPoints, zeroLocus, Set.mem_ofPred_eq]
    have hx : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) =
        (eval x g : ℚ) := by
      exact (map_eval (Int.castRingHom ℚ) x g).symm
    rw [hx, Int.cast_eq_zero, hzero]
    rfl
  have h := hbound g htop (by omega) B hB
  simpa only [hdeg, count, hpoints] using h

end
end CCDN
