/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Plane.Plane
public import CCDN.Algebra.PolynomialPredicates
import CCDN.LowerBound.GridAffineLowerBound
import CCDN.LowerBound.GridProjectiveLowerBound
import CCDN.LowerBound.IntegerGridLowerBound
/-! The final existence statement of CCDN Section 6, including every positive
 degree and every affine ambient dimension at least two. The same equation
 and integer radius give both affine and projective lower bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma hypersurface_grid_lower_bound_numerics {d n B L : ℕ}
    (hn : 2 ≤ n) (hB : 1 ≤ B) (hdB : d ≤ 4 * n * B) (hBL : B ≤ L) :
    ((d : ℝ) ^ 2 / (16 * (n : ℝ) ^ 2)) * (B : ℝ) ^ (n - 2) ≤ (L : ℝ) ^ n ∧
      ((d : ℝ) / (16 * (n : ℝ) ^ 2)) * (B : ℝ) ^ (n - 1) ≤ (L : ℝ) ^ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≤ 4 * n * B := by exact_mod_cast hdB
  have hden : (0 : ℝ) < 16 * (n : ℝ) ^ 2 := by positivity
  have hsquare : (d : ℝ) ^ 2 / (16 * (n : ℝ) ^ 2) ≤ (B : ℝ) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg d) hdR 2
    nlinarith
  have hlinear : (d : ℝ) / (16 * (n : ℝ) ^ 2) ≤ B := by
    apply (div_le_iff₀ hden).mpr
    have hh : 4 * (n : ℝ) ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg B)
    nlinarith
  have hlarge : (B : ℝ) ^ n ≤ (L : ℝ) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg B) (by exact_mod_cast hBL) n
  constructor
  · calc
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) ^ (n - 2) :=
        mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = (B : ℝ) ^ n := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := hlarge
  · calc
      _ ≤ (B : ℝ) * (B : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hlinear (by positivity)
      _ = (B : ℝ) ^ n := by rw [← pow_succ']; congr 1; omega
      _ ≤ _ := hlarge

/-- For every degree `d ≥ 1` a single absolutely irreducible equation of degree `d` and a
single integer `B` give both lower bounds in the final paragraph of CCDN Section 6. The positive
constant is chosen before d, and the projective equation is the
homogenization of the affine equation. -/
theorem exists_hypersurface_lower_bounds_all_degrees (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d →
      ∃ (f : MvPolynomial (Fin n) ℚ) (B : ℕ), 1 ≤ B ∧
        f.totalDegree = d ∧ AbsolutelyIrreducibleRat f ∧
        (scaledHomogenize d 1 f).IsHomogeneous d ∧
        (scaledHomogenize d 1 f).totalDegree = d ∧
        AbsolutelyIrreducibleRat (scaledHomogenize d 1 f) ∧
        c * (d : ℝ) ^ 2 * (B : ℝ) ^ (n - 2) ≤ (count (zeroLocus f) B : ℝ) ∧
        c * (d : ℝ) * (B : ℝ) ^ (n - 1) ≤
          (projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) B : ℝ) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨1 / (16 * (n : ℝ) ^ 2), by positivity, ?_⟩
  intro d hd
  let R := (d - 1) / (2 * n)
  let B := max 1 R
  let s : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hB : 1 ≤ B := le_max_left _ _
  have hRB : R ≤ B := le_max_right _ _
  have hBL : B ≤ 2 * R + 1 := by dsimp [B]; omega
  have hs : s.card = 2 * R + 1 := by rw [Int.card_Icc]; omega
  have hdB : d ≤ 4 * n * B := by
    have hdiv : d - 1 < (R + 1) * (2 * n) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * n)).mp (Nat.lt_succ_self R)
    have hfirst : d ≤ (R + 1) * (2 * n) := by omega
    have hnext := Nat.mul_le_mul_right (2 * n) (show R + 1 ≤ 2 * B by omega)
    nlinarith
  obtain ⟨f, hdeg, hir, hzero⟩ := exists_absolutely_irreducible_integer_grid d n hd hn
  have hsB (a) (ha : a ∈ s) : |(a : ℝ)| ≤ (B : ℝ) := by
    have haR : |a| ≤ (R : ℤ) := abs_le.mpr (Finset.mem_Icc.mp ha)
    have hh : |a| ≤ (B : ℤ) := haR.trans (by exact_mod_cast hRB)
    exact_mod_cast hh
  have hfzero (z : IntPoint n) (hz : ∀ j, z j ∈ s) : eval (rationalPoint z) f = 0 :=
    hzero z (fun j => abs_le.mpr (Finset.mem_Icc.mp (hz j)))
  have hca := integer_grid_le_affine_count f s hsB hfzero
  have hcp := integer_grid_le_projective_count f hdeg.le s (by exact_mod_cast hB) hsB hfzero
  rw [hs] at hca hcp
  obtain ⟨ha, hp⟩ := hypersurface_grid_lower_bound_numerics hn hB hdB hBL
  obtain ⟨hhom, hFdeg, hFir⟩ := projective_closure_absolute_irreducible f hdeg hir
  refine ⟨f, B, hB, hdeg, hir, hhom, hFdeg, hFir, ?_, ?_⟩
  · have hcR : ((2 * R + 1 : ℕ) : ℝ) ^ n ≤ (count (zeroLocus f) B : ℝ) := by
      exact_mod_cast hca
    have hh := ha.trans hcR
    simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using hh
  · have hcR : ((2 * R + 1 : ℕ) : ℝ) ^ n ≤
        (projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) B : ℝ) := by
      exact_mod_cast hcp
    have hh := hp.trans hcR
    simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using hh

end
end CCDN
