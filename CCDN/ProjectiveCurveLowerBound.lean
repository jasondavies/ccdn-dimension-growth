module

public import CCDN.GridProjectiveLowerBound
public import CCDN.GridLowerBoundNumerics

/-! CCDN Proposition 5 with its exact constant 1/5, for an absolutely
irreducible projective plane equation. The principal ideal is prime and its
projective Hilbert degree is the prescribed degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For every d>0 there is an absolutely irreducible projective plane curve
of degree d and an integer B≥1 with N(X,B)≥d² B^(2/d)/5. -/
theorem projective_plane_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) ∧
          ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
            (projectiveCount (projectiveZeroLocus F) B : ℝ) := by
  by_cases hlarge : 4 ≤ d
  · obtain ⟨F, hhom, hdeg, hir, hcount⟩ := exists_projective_grid_lower_bound d hlarge
    rw [grid_lower_bound_radius_identity d hd] at hcount
    refine ⟨F, (d + 1) / 4, grid_lower_bound_radius_pos (by omega), hhom, hdeg, hir, ?_⟩
    apply (grid_square_card_lower_bound hd (by positivity)
      (grid_lower_bound_radius_size d)).trans
    exact_mod_cast hcount
  · obtain ⟨F, hhom, hdeg, hir, hcount⟩ := exists_projective_two_point_lower_bound d hd
    refine ⟨F, 1, le_rfl, hhom, hdeg, hir, ?_⟩
    have hcountR : (2 : ℝ) ≤ projectiveCount (projectiveZeroLocus F) 1 := by exact_mod_cast hcount
    have hdR : (d : ℝ) ≤ 3 := by exact_mod_cast (show d ≤ 3 by omega)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    nlinarith [mul_nonneg hd0 (show 0 ≤ 3 - (d : ℝ) by linarith)]

/-- The lower-bound equation defines an integral homogeneous plane curve
whose degree is also certified by the projective Hilbert function. -/
theorem projective_integral_curve_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) ∧
          (Ideal.span {F}).IsPrime ∧ HasProjectiveCurveDegree (Ideal.span {F}) d ∧
            ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
              (projectiveCount (projectiveIdealZeroLocus (Ideal.span {F})) B : ℝ) := by
  obtain ⟨F, B, hB, hhom, hdeg, habs, hcount⟩ := projective_plane_lower_bound d hd
  have hir : Irreducible F :=
    mvPolynomial_irreducible_of_field_map (algebraMap ℚ (AlgebraicClosure ℚ)) F habs
  refine ⟨F, B, hB, hhom, hdeg, habs, Ideal.isPrime_span_singleton_of_prime hir.prime,
    principal_plane_hasProjectiveCurveDegree F hhom hir.ne_zero, ?_⟩
  rwa [projectiveIdealZeroLocus_span_singleton F hhom]

end
end CCDN
