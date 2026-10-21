/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.ResidueLinearCount
import CCDNPaper.Surface.PrimeWindowSalbergerRate

/-! The residue-edge remainder with the precise Salberger exponent.
The constants depend only on the surface degree and the fixed height and
auxiliary constants, and precede the equation and radius. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- For a degree `d ≥ 1` and constants `K, A ≥ 0`, there are `C, c > 0` such that, for every
integer surface equation `f` of degree `d` irreducible over `ℚ`, every congruence family with
constant `A`, and every family of curves on the surface, the residual locus of the residue cover
with prime window `surfaceResidueWindow d K B` and cutoff `2 B^(1/√d)` has at most
`C B^(2/√d + c/log(1 + log B))` integral points of height at most `B`. -/
theorem surface_residue_salberger_count (d : ℕ) (hd : 1 ≤ d)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), f.totalDegree = d →
      ∀ B : ℝ, ∀ hB : 1 ≤ B, ∀ F : SurfaceCongruenceFamily f B A,
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ S, IsSurfaceCurve (MvPolynomial.map (Int.castRingHom ℚ) f) I (δ I)) →
      (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) (surfaceResidueWindow_one_le d hK hB)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  have hscale := surfaceResidueWindowScale_two_le d hK
  have hlogscale := surfaceResidueLogScale_one_le d hK
  have hratio := scalingPrimeRatio_one_le
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let U := scalingPrimeRatio * surfaceResidueWindowScale d K + 1
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  obtain ⟨C₀, c₀, hC₀, hc₀, hbound⟩ := congruencePrimeWindow_edge_polylog_salberger_weight
    (show 1 ≤ surfaceResidueWindowScale d K by linarith)
    (show 1 ≤ 2 * (d : ℝ) by linarith) 4
  let E := 8 * (d : ℝ) * A ^ 2 * (surfaceResidueLogScale d K) ^ 2 * U ^ 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨E * C₀ + 1, c₀, by positivity, hc₀, ?_⟩
  intro f hfd B hB F hir S δ hS
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hL := surfaceResidueWindow_one_le d hK hB
  have hpoly := surface_residue_residual_count_le F hA hB hL
    (by omega : 1 ≤ f.totalDegree)
    (show 0 ≤ 2 * B ^ (1 / Real.sqrt (d : ℝ)) by positivity)
    (by rw [hfd]; nlinarith [Real.rpow_pos_of_pos hB0 (1 / Real.sqrt (d : ℝ))])
    hir S δ hS
  rw [hfd, surfaceResidueLogBudget_window] at hpoly
  have hu : scalingPrimeRatio * surfaceResidueWindow d K B + 1 ≤
      U * (Real.log B + 1) := by
    dsimp only [surfaceResidueWindow, U]
    nlinarith
  have hx : (2 * B ^ (1 / Real.sqrt (d : ℝ))) ^ 2 =
      4 * B ^ (2 / Real.sqrt (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (B ^ (1 / Real.sqrt (d : ℝ))) 2,
      ← Real.rpow_mul hB0.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  rw [hx] at hpoly
  have hestimate :
      (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) hL) B : ℝ) ≤
      E * (((congruencePrimeWindow (surfaceResidueWindow d K B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4) := by
    calc
      _ ≤ _ := hpoly
      _ ≤ 2 * (d : ℝ) * A ^ 2 *
          (surfaceResidueLogScale d K * (Real.log B + 1)) ^ 2 *
          (U * (Real.log B + 1)) ^ 2 *
          (4 * B ^ (2 / Real.sqrt (d : ℝ))) *
          (congruencePrimeWindow (surfaceResidueWindow d K B)).card *
          (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card := by
        gcongr
      _ = _ := by dsimp only [E]; ring
  have hh := mul_le_mul_of_nonneg_left (hbound (2 / Real.sqrt (d : ℝ)) B hB) hE
  have hfinal : (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) hL) B : ℝ) ≤
      E * (C₀ * B ^ (2 / Real.sqrt (d : ℝ) + c₀ / Real.log (1 + Real.log B))) :=
    hestimate.trans hh
  nlinarith [Real.rpow_pos_of_pos hB0 (2 / Real.sqrt (d : ℝ) + c₀ / Real.log (1 + Real.log B))]

end
end CCDN
