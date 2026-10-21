/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Analysis.DegreeDependenceNumerics
import CCDN.ProjectiveCurveLowerBound
/-! The degree factor in a coefficient-uniform projective curve bound cannot
be o(d²). The proof applies the upper bound to the curves constructed
for CCDN Proposition 5. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Filter Asymptotics

theorem projective_curve_factor_lower_bound {g : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ F : MvPolynomial (Fin 3) ℚ,
      F.IsHomogeneous F.totalDegree →
      AbsolutelyIrreducibleRat F →
      0 < F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * g F.totalDegree * B ^ (2 / (F.totalDegree : ℝ)))
    (d : ℕ) (hd : 0 < d) :
    (d : ℝ) ^ 2 / 5 ≤ C * g d := by
  obtain ⟨F, B, hB, hhom, hdeg, hir, hlo⟩ := projective_plane_lower_bound d hd
  have hupper := hbound F (hdeg ▸ hhom) hir (by omega) B (by exact_mod_cast hB)
  rw [hdeg] at hupper
  have hpos : (0 : ℝ) < (B : ℝ) ^ (2 / (d : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < B by omega)) _
  exact (mul_le_mul_iff_left₀ hpos).mp (hlo.trans hupper)

/-- Even restricting to absolutely irreducible plane curves, the factor
multiplying B^(2/d) cannot have subquadratic little-oh dependence on d. -/
theorem projective_curve_factor_not_isLittleO {g : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ F : MvPolynomial (Fin 3) ℚ,
      F.IsHomogeneous F.totalDegree →
      AbsolutelyIrreducibleRat F →
      0 < F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * g F.totalDegree * B ^ (2 / (F.totalDegree : ℝ))) :
    ¬ g =o[atTop] (fun d : ℕ => (d : ℝ) ^ 2) := by
  apply not_isLittleO_of_eventually_lower_bound (c := 1 / 5) (by norm_num) hC
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with d hd
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      projective_curve_factor_lower_bound hbound d (by omega)

/-- A power of the degree in a uniform projective curve bound must have
exponent at least two. -/
theorem projective_curve_degree_exponent_ge_two {e C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ F : MvPolynomial (Fin 3) ℚ,
      F.IsHomogeneous F.totalDegree →
      AbsolutelyIrreducibleRat F →
      0 < F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * (F.totalDegree : ℝ) ^ e * B ^ (2 / (F.totalDegree : ℝ))) :
    2 ≤ e := by
  by_contra h
  have hh := natCast_rpow_isLittleO_of_lt (lt_of_not_ge h)
  exact projective_curve_factor_not_isLittleO hC hbound
    (by simpa only [Real.rpow_two] using hh)

end
end CCDN
