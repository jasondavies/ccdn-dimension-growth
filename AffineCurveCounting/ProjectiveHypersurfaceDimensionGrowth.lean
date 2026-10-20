module

public import AffineCurveCounting.ProjectiveHypersurfaceGrowth
public import AffineCurveCounting.NonabsoluteHypersurfaceCount

/-! Projective dimension growth for rationally irreducible hypersurfaces.
The geometrically irreducible and nonabsolute cases are both included,
with one constant chosen before the equation and the height. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

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

/-- Large-degree CCDN dimension growth for every rationally irreducible
projective hypersurface in projective space of dimension at least two.
Absolute irreducibility is not an assumption of this endpoint. -/
theorem projective_hypersurface_dimension_growth_large_degree (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℚ,
      f.IsHomogeneous f.totalDegree → Irreducible f →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := projective_hypersurface_count_large_degree n
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
end AffineCurveCounting
