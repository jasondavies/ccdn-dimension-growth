/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.HyperplaneSlicingInduction
public import CCDN.Surface.AffineSurfaceDimensionGrowth
public import CCDN.Algebra.PolynomialPredicates
/-! CCDN Theorem 4 with the corrected degree exponent of Remark 4.3.8.
In `N = n + 3` variables the exponent is `18 + 3n = 3N + 9`: the corrected surface
bound `d^18` and a cost of `d^3` for each bounded good hyperplane slice. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational-equation form of `AffineHypersurfaceGrowth`. -/
def RationalAffineHypersurfaceGrowth (n e : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ f : MvPolynomial (Fin (n + 3)) ℚ, HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        (count (zeroLocus f) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)

/-- Clearing denominators transfers affine dimension growth from integer equations to
rational equations with the same constant. -/
theorem AffineHypersurfaceGrowth.rational {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    RationalAffineHypersurfaceGrowth n e := by
  classical
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun f hir hd B hB => ?_⟩
  obtain ⟨g, hdeg, htop, hzero⟩ := exists_integer_model_absolute_top f hir
  have hpoints : integralPoints (zeroLocus (map (Int.castRingHom ℚ) g)) B =
      integralPoints (zeroLocus f) B := by
    ext x
    simp only [mem_integralPoints, zeroLocus, Set.mem_ofPred_eq]
    have hx : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = (eval x g : ℚ) :=
      (map_eval (Int.castRingHom ℚ) x g).symm
    rw [hx, Int.cast_eq_zero, hzero]
    rfl
  simpa only [hdeg, count, hpoints] using hbound g htop (by omega) B hB

theorem affineHypersurfaceGrowth (n : ℕ) : AffineHypersurfaceGrowth n (18 + 3 * n) :=
  affineHypersurfaceGrowth_of_surface (by
    simpa only [AffineHypersurfaceGrowth, Nat.zero_add, pow_one]
      using affine_surface_dimension_growth) n

/-- CCDN Theorem 4 for integer equations in all affine ambient dimensions
at least three. The constant depends only on dimension, and the explicit
degree exponent is 18 + 3n in n+3 variables. -/
theorem affine_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) :=
  affineHypersurfaceGrowth n

/-- CCDN Theorem 4 for rational equations, with the degree exponent 18 + 3n in
n+3 variables. -/
theorem affine_hypersurface_dimension_growth_rat (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 3 * n) * B ^ (n + 1) :=
  (affineHypersurfaceGrowth n).rational

end
end CCDN
