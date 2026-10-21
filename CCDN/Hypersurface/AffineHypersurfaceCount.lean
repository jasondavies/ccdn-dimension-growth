/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
public import CCDN.Hypersurface.HyperplaneSlicingInduction
import CCDN.Hypersurface.IntegerGoodHyperplaneSlices
import CCDN.Surface.AffineSurfaceDimensionGrowth
/-! Affine hypersurface dimension growth with the corrected degree exponent: the surface bound
`d^18` of Proposition 4.3.4 starts the hyperplane-slicing induction, which costs `d^3` for each
further variable, and clearing denominators passes from integer to rational equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

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

end
end CCDN
