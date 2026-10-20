module

public import CCDN.TopFormDimensionGrowth
public import CCDN.ProjectiveConeBound

/-! Large-degree dimension growth for rational affine equations with absolutely
irreducible leading form, and for absolutely irreducible projective
hypersurfaces. Denominator clearing preserves the integer zero set. Primitive
projective representatives then inject into the affine cone at the same height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational-equation version of the large-degree affine bound. -/
theorem rational_top_form_hypersurface_count_large_degree (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := top_form_hypersurface_count_large_degree n
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB
  obtain ⟨g, hdeg, htop, hzero⟩ := exists_integer_model_absolute_top f hir
  have hpoints : integralPoints (zeroLocus (map (Int.castRingHom ℚ) g)) B =
      integralPoints (zeroLocus f) B := by
    ext x
    simp only [mem_integralPoints, zeroLocus, Set.mem_ofPred_eq]
    have hx : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) =
        (eval x g : ℚ) := by
      exact (map_eval (Int.castRingHom ℚ) x g).symm
    rw [hx, Int.cast_eq_zero, hzero]
    rfl
  have h := hbound g htop (by omega) B hB
  simpa only [hdeg, count, hpoints] using h

/-- Theorem 1 for geometrically integral hypersurfaces of degree at least
sixteen in projective space of dimension at least two. The exponent of the
height is the hypersurface dimension. -/
theorem projective_hypersurface_count_large_degree (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      f.IsHomogeneous f.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := rational_top_form_hypersurface_count_large_degree n
  refine ⟨C, hC, ?_⟩
  intro f hhom hir hd B hB
  have htop : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (homogeneousComponent f.totalDegree f)) := by
    rwa [homogeneousComponent_eq_self hhom]
  exact (Nat.cast_le.mpr (projective_count_le_affine_cone_count f hhom B)).trans
    (hbound f htop hd B hB)

end
end CCDN
