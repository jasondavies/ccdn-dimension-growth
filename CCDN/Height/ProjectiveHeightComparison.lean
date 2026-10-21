/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.Box
public import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.Determinant.HomogeneousDeterminantComparison
import CCDN.Determinant.ProjectiveHeightDeterminant
/-! The coefficient-sensitive determinant comparison for bounded primitive
integer representatives of projective plane points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projective_no_auxiliary_height_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d) (hdM : d ≤ M)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) -
          heightDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
      hzB.one_le_radius hzB.abs_le hrel
  have hs := (plane_homogeneous_rank_bounds (by omega : 0 < d) hdM hr).1
  refine ⟨s, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let F := fun j => (monomial (homogeneousMonomials 2 M j) 1 : MvPolynomial (Fin 3) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree 2 M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials 2 M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hi
  have hlower := projective_determinant_log_lower_height (z := z ∘ a) hs f hf hd hchart
    ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩
  rw [he] at hlower
  exact hlower.trans hupper

end
end CCDN
