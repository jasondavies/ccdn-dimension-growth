/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.Box
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
    (hdeg : (affineChart 2 f).totalDegree = d)
    (hir : Irreducible (map (Int.castRingHom K) (affineChart 2 f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((affineChart 2 f).coeff m : ℝ)| ≤ H)
    (z : Fin t → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
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
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hz hB hbox hrel
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
  have hlower := projective_determinant_log_lower_height hs f hf hd hdeg hir H hH hcoeff
    F hF (z ∘ a) (fun i => hprim (a i)) (fun i => hz (a i)) hi'
  rw [he] at hlower
  exact hlower.trans hupper

end
end CCDN
