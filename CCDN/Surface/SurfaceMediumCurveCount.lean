/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Curve.SmallDegreeSurfaceCurveCount
public import CCDN.Surface.LogarithmicSalbergerRate
/-! Curves between a fixed degree cutoff and the logarithmic terminal
cutoff can be left in the exceptional set. Their aggregate count has the
required B^(2/sqrt d) scale with a fixed logarithmic factor. -/

@[expose] public section
namespace CCDN
noncomputable section

theorem curveBound_medium_degree {δ d : ℕ} (hd : 1 ≤ d) (hδ : d ≤ δ)
    {B D : ℝ} (hB : 1 ≤ B) (_hD : 0 ≤ D)
    (hδD : (δ : ℝ) ≤ D * (Real.log B + 1)) :
    curveBound δ B ≤ (δ : ℝ) * D ^ 2 * (D + 1) *
      B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 3 := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog := Real.log_nonneg hB
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hδR : (d : ℝ) ≤ δ := by exact_mod_cast hδ
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsle : Real.sqrt (d : ℝ) ≤ δ := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
    have hsn := Real.sqrt_nonneg (d : ℝ)
    nlinarith
  have hpow : B ^ (1 / (δ : ℝ)) ≤ B ^ (1 / Real.sqrt (d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le hs hsle)
  have hsq : (δ : ℝ) ^ 2 ≤ (D * (Real.log B + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hδD 2
  have hlogδ : Real.log B + δ ≤ (D + 1) * (Real.log B + 1) := by nlinarith
  have hcube : (δ : ℝ) ^ 3 ≤ (δ : ℝ) * (D * (Real.log B + 1)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ δ by positivity)
    nlinarith
  unfold curveBound
  calc
    _ ≤ ((δ : ℝ) * (D * (Real.log B + 1)) ^ 2) *
        B ^ (1 / Real.sqrt (d : ℝ)) * ((D + 1) * (Real.log B + 1)) := by
      apply mul_le_mul (mul_le_mul hcube hpow (by positivity) (by positivity)) hlogδ
      · positivity
      · positivity
    _ = _ := by ring

/-- An absolute curve constant, with the surface degree and all family
parameters quantified afterwards. -/
theorem medium_degree_curve_union_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (d : ℕ), 1 ≤ d →
      ∀ A D B : ℝ, 0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ P ∈ S, P.IsPrime ∧ d ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∀ P ∈ S, (δ P : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ P ∈ S, (δ P : ℝ)) ≤ A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        C * A * D ^ 2 * (D + 1) * B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4 := by
  obtain ⟨C,hC,hcount⟩ := affineCurveBound 3 (by omega)
  refine ⟨C,hC,?_⟩
  intro S δ d hd A D B hA hD hB hcurve hcap hbudget
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlog := Real.log_nonneg hB
  calc
    _ ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
    _ ≤ ∑ P ∈ S, C * ((δ P : ℝ) * D ^ 2 * (D + 1) *
        B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 3) := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hp,hδ,hdeg⟩ := hcurve P hP
      exact (hcount P hp (δ P) (by omega) hdeg B hB).trans
        (mul_le_mul_of_nonneg_left (curveBound_medium_degree hd hδ hB hD (hcap P hP)) hC.le)
    _ = C * (∑ P ∈ S, (δ P : ℝ)) * D ^ 2 * (D + 1) *
        B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 3 := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ ≤ C * (A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) *
        D ^ 2 * (D + 1) * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 3 := by
      gcongr
    _ = _ := by
      have he : B ^ (2 / Real.sqrt (d : ℝ)) =
          B ^ (1 / Real.sqrt (d : ℝ)) * B ^ (1 / Real.sqrt (d : ℝ)) := by
        rw [← Real.rpow_add hB0]
        congr 1
        ring
      rw [he]
      ring

end
end CCDN
