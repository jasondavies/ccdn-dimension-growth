/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.Plane
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Analysis.DegreeDependenceNumerics
import CCDN.LowerBound.GridAffineLowerBound
import CCDN.LowerBound.GridLowerBoundNumerics
import CCDN.LowerBound.IntegerGridLowerBound
/-! The affine-curve sharpness statement in CCDN Section 6, with
absolutely irreducible equations through the specified integer grids. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Filter Asymptotics

lemma log_sq_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ x := by
  have hxpos : 0 < x := by linarith
  let t := x ^ (1 / 4 : ℝ)
  have htpos : 0 < t := Real.rpow_pos_of_pos hxpos _
  have htlog := Real.log_le_sub_one_of_pos htpos
  have htlog' : Real.log x ≤ 4 * (t - 1) := by
    dsimp [t] at htlog
    rw [Real.log_rpow hxpos] at htlog
    linarith
  have hlog : Real.log x ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 2)]
  have hlog0 := Real.log_nonneg hx
  have ht4 : (t ^ 2) ^ 2 = x := by
    dsimp [t]
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  calc
    (Real.log x) ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
    _ = x := ht4

/-- The chosen grid radius satisfies the exact logarithmic comparison
used in the affine conclusion of Section 6. -/
lemma grid_radius_rpow_mul_log_le_log_degree {d : ℕ} (hd : 3 ≤ d)
    {B : ℝ} (hB : 1 ≤ B) (hsize : 4 * B ≤ (d : ℝ) + 1) :
    B ^ (1 / (d : ℝ)) * Real.log B ≤ Real.log d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hBpos : 0 < B := by linarith
  have hBlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hBd : 3 * B ≤ (d : ℝ) := by linarith
  let x := B ^ (1 / (d : ℝ))
  have hxpos : 0 < x := Real.rpow_pos_of_pos hBpos _
  have hxbound : x ≤ 5 / 4 := by
    apply le_trans (Real.rpow_le_rpow_of_exponent_le hB ?_)
      (grid_radius_rpow_le_five_fourths (by omega) hBpos.le hsize)
    exact div_le_div_of_nonneg_right (by norm_num) hdpos.le
  have hxlog := Real.one_sub_inv_le_log_of_pos hxpos
  have hxlin : x - 1 ≤ x * ((1 / (d : ℝ)) * Real.log B) := by
    have hh := mul_le_mul_of_nonneg_left hxlog hxpos.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hxpos.ne'] at hh
    simpa only [x, Real.log_rpow hBpos] using hh
  have hsq := log_sq_le_self_of_one_le hB
  have hinc : (x - 1) * Real.log B ≤ (5 / 4 : ℝ) * B / d := by
    calc
      _ ≤ (x * ((1 / (d : ℝ)) * Real.log B)) * Real.log B :=
        mul_le_mul_of_nonneg_right hxlin hBlog
      _ = (x / (d : ℝ)) * (Real.log B) ^ 2 := by ring
      _ ≤ (x / (d : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ ((5 / 4 : ℝ) / d) * B :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hxbound hdpos.le) hBpos.le
      _ = _ := by ring
  have hratio := Real.one_sub_inv_le_log_of_pos (div_pos hdpos hBpos)
  have hgap : 1 - B / d ≤ Real.log d - Real.log B := by
    simpa only [inv_div, Real.log_div hdpos.ne' hBpos.ne'] using hratio
  have hsmall : (5 / 4 : ℝ) * B / d ≤ 1 - B / d := by
    apply (div_le_iff₀ hdpos).mpr
    have he : (1 - B / (d : ℝ)) * d = (d : ℝ) - B := by field_simp
    rw [he]
    linarith
  dsimp [x] at hinc
  nlinarith [hinc.trans (hsmall.trans hgap)]

theorem exists_affine_curve_log_lower_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ f : MvPolynomial (Fin 2) ℚ, ∃ B : ℕ,
      B = (d + 1) / 4 ∧ 1 ≤ B ∧ f.totalDegree = d ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) ∧
      ((d : ℝ) ^ 2 / (4 * Real.log d)) *
          (B : ℝ) ^ (1 / (d : ℝ)) * Real.log B ≤
        (count (zeroLocus f) B : ℝ) := by
  by_cases hlarge : 4 ≤ d
  swap
  · have hd3 : d = 3 := by omega
    subst d
    obtain ⟨f, hdeg, hir, _⟩ := exists_irreducible_origin_equation
      (algebraMap ℚ (AlgebraicClosure ℚ)) 3 2 (by omega) (by omega)
    refine ⟨f, 1, by norm_num, le_rfl, hdeg, hir, ?_⟩
    simp
  obtain ⟨f, hfdeg, hfir, hgrid⟩ := exists_affine_plane_grid_lower_bound d hlarge
  let B := (d + 1) / 4
  have hB : 1 ≤ B := grid_lower_bound_radius_pos (by omega)
  have hdpos : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hlogpos : 0 < Real.log d := Real.log_pos hdpos
  have hnum := grid_radius_rpow_mul_log_le_log_degree (by omega : 3 ≤ d)
    (by exact_mod_cast hB : (1 : ℝ) ≤ B) (grid_lower_bound_radius_size d)
  have hds : d ≤ 2 * ((d - 1) / 2 + 1) := by omega
  have hdsR : (d : ℝ) ≤ 2 * (((d - 1) / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hds
  have hsquare : (d : ℝ) ^ 2 / 4 ≤ (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg d) hdsR 2
    nlinarith
  refine ⟨f, B, rfl, hB, hfdeg, hfir, ?_⟩
  calc
    _ = ((d : ℝ) ^ 2 / (4 * Real.log d)) *
        ((B : ℝ) ^ (1 / (d : ℝ)) * Real.log B) := by ring
    _ ≤ ((d : ℝ) ^ 2 / (4 * Real.log d)) * Real.log d :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = (d : ℝ) ^ 2 / 4 := by field_simp
    _ ≤ (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := hsquare
    _ ≤ _ := by exact_mod_cast hgrid

theorem affine_curve_log_factor_lower_bound {g : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ f : MvPolynomial (Fin 2) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) →
      2 ≤ f.totalDegree → ∀ B : ℝ, 2 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * g f.totalDegree * B ^ (1 / (f.totalDegree : ℝ)) * Real.log B)
    (d : ℕ) (hd : 7 ≤ d) :
    (d : ℝ) ^ 2 / (4 * Real.log d) ≤ C * g d := by
  obtain ⟨f, B, hBradius, hB, hfdeg, hfir, hlo⟩ :=
    exists_affine_curve_log_lower_bound d (by omega)
  have hB2 : (2 : ℝ) ≤ B := by
    exact_mod_cast (show 2 ≤ B by omega)
  have hu := hbound f hfir (by omega) B hB2
  rw [hfdeg] at hu
  have hlogpos : 0 < Real.log B := Real.log_pos (by linarith)
  have hpowpos : (0 : ℝ) < (B : ℝ) ^ (1 / (d : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  exact (mul_le_mul_iff_left₀ hpowpos).mp
    ((mul_le_mul_iff_left₀ hlogpos).mp (hlo.trans hu))

/-- In a coefficient-uniform affine curve bound of the form
C g(d) B^(1/d) log B for B≥2, the degree factor cannot be o(d²/log d).
This is the logarithmic envelope of the bound discussed in CCDN Section 6. -/
theorem affine_curve_log_factor_not_isLittleO {g : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ f : MvPolynomial (Fin 2) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) →
      2 ≤ f.totalDegree → ∀ B : ℝ, 2 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * g f.totalDegree * B ^ (1 / (f.totalDegree : ℝ)) * Real.log B) :
    ¬ g =o[atTop] (fun d : ℕ => (d : ℝ) ^ 2 / Real.log d) := by
  apply not_isLittleO_of_eventually_lower_bound (c := 1 / 4) (by norm_num) hC
  · filter_upwards [eventually_ge_atTop 2] with d hd
    have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    have : 0 < Real.log d := Real.log_pos hdR
    positivity
  · filter_upwards [eventually_ge_atTop 7] with d hd
    have h := affine_curve_log_factor_lower_bound hbound d hd
    convert h using 1
    ring

end
end CCDN
