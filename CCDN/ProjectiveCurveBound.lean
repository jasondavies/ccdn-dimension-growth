/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectiveProjectionCount
public import CCDN.Algebra.ProjectivePermutation
public import CCDN.Projection.ProjectionScaleAbsorption
/-! CCDN Theorem 2 in every ambient dimension. Degree is the slope of
the homogeneous Hilbert function. The height and count use rational
projective points. All projection and plane-counting inputs are proved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def projectiveCurveEstimate (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ))

def projectiveCurveConstant (n : ℕ) : ℝ :=
  projectivePlaneAbsoluteConstant * Real.exp (2 * projectionLogConstant n) + 1

lemma projectiveCurveConstant_pos (n : ℕ) : 0 < projectiveCurveConstant n := by
  unfold projectiveCurveConstant
  have := projectivePlaneAbsoluteConstant_pos
  positivity

theorem projectiveCurveEstimate_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
      Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < projectionBoxFactor n d := lt_of_lt_of_le (by norm_num) (projectionBoxFactor_one_le n d)
  have hpow : (projectionBoxFactor n d) ^ (2 / (d : ℝ)) ≤
      Real.exp (2 * projectionLogConstant n) := by
    rw [Real.rpow_def_of_pos hA, Real.exp_le_exp, ← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    have hlog := projectionBoxFactor_log_le n hd
    linarith
  unfold projectiveCurveEstimate
  rw [Real.mul_rpow hA.le (by linarith)]
  have h := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by positivity)
  convert h using 1 <;> ring

theorem projective_curve_count_of_proper_chart {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  obtain ⟨f, hf, hir, hreduce⟩ := exists_projective_plane_count_reduction I hX hd hdegree
  have hAB := one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hplane := projective_plane_equation_bound f hf hd hir hAB
  have hR : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + (d : ℝ) ^ 2 := by
    exact_mod_cast hreduce B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have herr : (d : ℝ) ^ 2 ≤ projectiveCurveEstimate d B :=
    (pow_le_pow_right₀ hd1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) hQ)
  calc
    _ ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) +
        (d : ℝ) ^ 2 := hR
    _ ≤ projectivePlaneAbsoluteConstant *
          projectiveCurveEstimate d (projectionBoxFactor n d * B) +
        projectiveCurveEstimate d B := by
      rw [projectiveCurveEstimate, ← mul_assoc]
      exact add_le_add hplane herr
    _ ≤ projectivePlaneAbsoluteConstant *
          (Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B) +
        projectiveCurveEstimate d B := by
      gcongr
      exacts [projectivePlaneAbsoluteConstant_pos.le, projectiveCurveEstimate_scale n hd hB]
    _ = projectiveCurveConstant n * projectiveCurveEstimate d B := by
      unfold projectiveCurveConstant
      ring

/-- The coordinate chart is chosen from a point when the counted
set is nonempty. Coordinate permutation has no height cost. -/
theorem projective_curve_count {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  classical
  by_cases hS : (projectivePoints (projectiveIdealZeroLocus I) B).Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hxI := (mem_projectivePoints.mp hx).2
    obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
    change x.rep j ≠ 0 at hj
    let e := Equiv.swap (0 : Fin (n + 1)) j
    let J := projectivePermutedIdeal I e
    have hX : X 0 ∉ J := by
      intro h
      have hh := (mem_projectivePermutedIdeal I e (X 0)).mp h
      have hXj : X j ∈ I := by simpa [e] using hh
      have hz := projectiveIdealZeroLocus_rep hxI (X j) hXj
      exact hj (by simpa using hz)
    have hJ := projectiveCurveDegree_permuted I e hdegree
    have h := projective_curve_count_of_proper_chart J hX hd hJ hB
    have hc : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        projectiveCount (projectiveIdealZeroLocus J) B := by
      exact_mod_cast projectiveCount_le_permuted I e B
    exact hc.trans h
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    unfold projectiveCount
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (projectiveCurveConstant_pos n).le
      (by unfold projectiveCurveEstimate; positivity)

/-- CCDN (2020), Theorem 2, with projective degree specified by the
homogeneous Hilbert function. The constant precedes the ideal, degree and radius. -/
def ProjectiveCurveBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (CoordinatePolynomial (n + 1)), I.IsPrime →
      ∀ d : ℕ, 0 < d → HasProjectiveCurveDegree I d →
        ∀ B : ℝ, 1 ≤ B →
          (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤ C * projectiveCurveEstimate d B

theorem projectiveCurveBound : ProjectiveCurveBound := by
  intro n _
  refine ⟨projectiveCurveConstant n, projectiveCurveConstant_pos n, ?_⟩
  intro I hI d hd hdegree B hB
  have : I.IsPrime := hI
  exact projective_curve_count I hd hdegree hB

end
end CCDN
