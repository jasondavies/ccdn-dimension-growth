module

public import CCDN.TopFormDimensionGrowthAllDegrees
public import CCDN.ProjectiveHypersurfaceDimensionGrowth

/-! Full CCDN affine hypersurface dimension growth and its projective
hypersurface consequence, in every degree at least five. Rational
coefficient clearing is constructed internally. The projective endpoint
also includes rationally irreducible equations which split geometrically. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational-equation version of the full affine bound. -/
theorem rational_top_form_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := top_form_hypersurface_dimension_growth n
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
five in projective space of dimension at least two. The exponent of the
height is the hypersurface dimension. -/
theorem absolute_projective_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      f.IsHomogeneous f.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := rational_top_form_hypersurface_dimension_growth n
  refine ⟨C, hC, ?_⟩
  intro f hhom hir hd B hB
  have htop : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (homogeneousComponent f.totalDegree f)) := by
    rwa [homogeneousComponent_eq_self hhom]
  exact (Nat.cast_le.mpr (projective_count_le_affine_cone_count f hhom B)).trans
    (hbound f htop hd B hB)


/-- CCDN Theorem 1 dimension growth in every degree at least five for every rationally irreducible
projective hypersurface in projective space of dimension at least two.
Absolute irreducibility is not an assumption of this endpoint. -/
theorem projective_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      f.IsHomogeneous f.totalDegree → Irreducible f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := absolute_projective_hypersurface_dimension_growth n
  let A : ℝ := (3 * (n + 3) : ℝ) ^ (n + 1)
  have hA : 0 ≤ A := by positivity
  refine ⟨C + A, by positivity, ?_⟩
  intro f hhom hir hd B hB
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by
    exact_mod_cast (show 1 ≤ f.totalDegree by omega)
  have hB0 : 0 ≤ B := by linarith
  by_cases habs : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f)
  · apply (hbound f hhom habs hd B hB).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + A) (by positivity))
      (pow_nonneg hB0 _)
  · have hh : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        A * (f.totalDegree : ℝ) ^ 2 * B ^ (n + 1) := by
      simpa only [A, Nat.cast_add, Nat.cast_one, add_assoc,
        show (1 : ℝ) + 2 = 3 by norm_num] using
        nonabsolute_projective_hypersurface_dimension_growth f hhom hir habs hB
    have hp : (f.totalDegree : ℝ) ^ 2 ≤
        (f.totalDegree : ℝ) ^ (18 + 9 * n) :=
      pow_le_pow_right₀ hd1 (by omega)
    calc
      _ ≤ A * (f.totalDegree : ℝ) ^ 2 * B ^ (n + 1) := hh
      _ ≤ (C + A) * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
        gcongr
        linarith


end
end CCDN
