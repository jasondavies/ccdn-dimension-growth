/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.Plane
import CCDN.Height.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes
/-! Removing integer content from the fixed-degree surface estimate.
The resulting constant is uniform in all integer coefficients. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every fixed degree at least five has a coefficient-uniform linear
integer-point bound when the highest homogeneous part is absolutely
irreducible. The equation need not be primitive. -/
theorem top_form_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := primitive_surface_fixed_degree_linear_bound d hd
  refine ⟨C, hC, ?_⟩
  intro f hir hfd B hB
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, hprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨hudeg, hutop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  have hzero : zeroLocus (map (Int.castRingHom ℚ) f) =
      zeroLocus (map (Int.castRingHom ℚ) u) := by
    ext x
    change eval x (map (Int.castRingHom ℚ) f) = 0 ↔
      eval x (map (Int.castRingHom ℚ) u) = 0
    rw [he, map_mul, map_C, eval_mul, eval_C]
    exact mul_eq_zero_iff_left (show (c : ℚ) ≠ 0 by exact_mod_cast hc)
  rw [hzero]
  exact hbound u hprim hutop (hudeg.trans hfd) B hB

end
end CCDN
