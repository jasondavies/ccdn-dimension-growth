/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AffineHypersurfaceDimensionGrowth
public import CCDN.Algebra.ProjectiveConeBound
public import CCDN.Hypersurface.NonabsoluteHypersurfaceCount
public import CCDN.Algebra.PolynomialPredicates
/-! Projective hypersurface dimension growth in every degree at least five, from the
affine bound on the cone. The equation need only be irreducible over `ℚ`: an equation which
splits over `ℚ̄` has few points by the nonabsolute count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Dimension growth with degree exponent `e` for rationally irreducible projective
hypersurfaces of degree at least five in `ℙ^(n+2)`. The height exponent is the
hypersurface dimension `n + 1`. -/
def ProjectiveHypersurfaceGrowth (n e : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ f : MvPolynomial (Fin (n + 3)) ℚ, f.IsHomogeneous f.totalDegree → Irreducible f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
          C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)

theorem nonabsolute_projective_hypersurface_dimension_growth {K : Type*}
    [Field K] [Algebra ℚ K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℚ)
    (hhom : f.IsHomogeneous f.totalDegree) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n :=
  (Nat.cast_le.mpr (projective_count_le_affine_cone_count f hhom B)).trans
    (nonabsolute_hypersurface_dimension_growth f hir hred hB)

/-- The affine bound on the cone gives the projective hypersurface bound with the same
degree exponent, provided the exponent is at least two. -/
theorem RationalAffineHypersurfaceGrowth.projective {n e : ℕ}
    (h : RationalAffineHypersurfaceGrowth n e) (he : 2 ≤ e) :
    ProjectiveHypersurfaceGrowth n e := by
  obtain ⟨C, hC, hbound⟩ := h
  let A : ℝ := (3 * (n + 3) : ℝ) ^ (n + 1)
  refine ⟨C + A, by positivity, fun f hhom hir hd B hB => ?_⟩
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast (show 1 ≤ f.totalDegree by omega)
  have hB0 : 0 ≤ B := by linarith
  by_cases habs : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f)
  · have htop : HasAbsIrreducibleTopFormRat f := by
      dsimp only [HasAbsIrreducibleTopFormRat]
      rwa [homogeneousComponent_eq_self hhom]
    calc
      _ ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) :=
        (Nat.cast_le.mpr (projective_count_le_affine_cone_count f hhom B)).trans
          (hbound f htop hd B hB)
      _ ≤ (C + A) * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · have hh : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        A * (f.totalDegree : ℝ) ^ 2 * B ^ (n + 1) := by
      simpa only [A, Nat.cast_add, Nat.cast_one, add_assoc,
        show (1 : ℝ) + 2 = 3 by norm_num] using
        nonabsolute_projective_hypersurface_dimension_growth f hhom hir habs hB
    calc
      _ ≤ A * (f.totalDegree : ℝ) ^ 2 * B ^ (n + 1) := hh
      _ ≤ (C + A) * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by
        gcongr
        linarith

/-- CCDN Theorem 1 for rationally irreducible projective hypersurfaces of degree at least
five in `ℙ^(n+2)`, with degree exponent `18 + 3n`. Unlike the paper, the equation may split
over `ℚ̄`. -/
theorem projective_hypersurface_dimension_growth (n : ℕ) :
    ProjectiveHypersurfaceGrowth n (18 + 3 * n) :=
  (affineHypersurfaceGrowth n).rational.projective (by omega)

end
end CCDN
