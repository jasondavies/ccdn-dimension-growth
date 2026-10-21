/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CCDN.Algebra.PolynomialPredicates
import CCDN.LowerBound.GridCurveConstruction
import CCDN.LowerBound.GridLowerBoundNumerics

/-! Affine counts supplied by finite Cartesian grids. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma integer_grid_le_affine_count {n : ℕ} (f : MvPolynomial (Fin n) ℚ)
    (s : Finset ℤ) {B : ℝ} (hsB : ∀ a ∈ s, |(a : ℝ)| ≤ B)
    (hfzero : ∀ z : IntPoint n, (∀ j, z j ∈ s) → eval (rationalPoint z) f = 0) :
    s.card ^ n ≤ count (zeroLocus f) B := by
  classical
  let S : Finset (IntPoint n) := Fintype.piFinset (fun _ => s)
  have hScard : S.card = s.card ^ n := by simp [S, Fintype.card_piFinset]
  rw [← hScard]
  apply Finset.card_le_card
  intro z hz
  have hz' : ∀ j, z j ∈ s := Fintype.mem_piFinset.mp hz
  apply mem_integralPoints.mpr
  exact ⟨fun j => hsB (z j) (hz' j), hfzero z hz'⟩

/-- A plane curve with exactly the degree and grid size used in Section 6.
This is a lower bound for the integral-point count. -/
theorem exists_affine_plane_grid_lower_bound (d : ℕ) (hd : 4 ≤ d) :
    ∃ f : MvPolynomial (Fin 2) ℚ,
      f.totalDegree = d ∧ AbsolutelyIrreducibleRat f ∧
        ((d - 1) / 2 + 1) ^ 2 ≤
          count (zeroLocus f) ((((d + 1) / 4 : ℕ)) : ℝ) := by
  classical
  let q := (d - 1) / 2
  let r := (d - 1) / 4
  let B := (d + 1) / 4
  have hB : B = q - r := (grid_lower_bound_radius_identity d (by omega)).symm
  have hrq : r ≤ q := by dsimp [q, r]; omega
  have hrB : r ≤ B := by dsimp [B, q, r]; omega
  let s : Finset ℤ := Finset.Icc (-(B : ℤ)) (r : ℤ)
  have hs : s.card = q + 1 := by rw [Int.card_Icc]; omega
  let t : Finset ℚ := s.image (Int.castRingHom ℚ)
  have ht : t.card = q + 1 := by
    change (s.image (fun x : ℤ => (x : ℚ))).card = _
    rw [Finset.card_image_of_injective _ Int.cast_injective, hs]
  obtain ⟨f, hfdeg, hfir, hfzero⟩ := exists_absolutely_irreducible_plane_grid
    (algebraMap ℚ (AlgebraicClosure ℚ)) t (by rw [ht]; omega) d
    (by rw [ht]; dsimp [q]; omega) (by rw [ht]; dsimp [q]; omega)
  refine ⟨f, hfdeg, hfir, ?_⟩
  change (q + 1) ^ 2 ≤ count _ (B : ℝ)
  rw [← hs]
  apply integer_grid_le_affine_count f s
  · intro a ha
    have hab := Finset.mem_Icc.mp ha
    have har : a ≤ (B : ℤ) := hab.2.trans (by exact_mod_cast hrB)
    exact_mod_cast abs_le.mpr ⟨hab.1, har⟩
  · intro z hz
    apply hfzero
    intro j
    exact Finset.mem_image.mpr ⟨z j, hz j, rfl⟩

end
end CCDN
