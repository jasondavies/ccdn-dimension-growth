module

public import CCDN.Surface.TopFormSurfaceFixedDegree
public import CCDN.Surface.AffineSurfaceCountLargeDegree
public import CCDN.Algebra.PolynomialPredicates
/-! The affine surface bound in every degree at least five. The finitely many
degrees below the large-degree threshold are absorbed in one constant. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The fixed-degree surface bounds for the degrees `5 ≤ d < t` hold with one constant. -/
theorem top_form_surface_bounded_degree_linear_bound (t : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → f.totalDegree < t → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  induction t with
  | zero => exact ⟨1, one_pos, fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    by_cases ht : 5 ≤ t
    · obtain ⟨C', hC', hbound'⟩ := top_form_surface_fixed_degree_linear_bound t ht
      refine ⟨C + C', by positivity, fun f hir hd hlt B hB => ?_⟩
      have hB0 : 0 ≤ B := by linarith
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
      · exact (hbound f hir hd hlt B hB).trans (by gcongr; linarith)
      · exact (hbound' f hir heq B hB).trans (by gcongr; linarith)
    · exact ⟨C, hC, fun f hir hd hlt => hbound f hir hd (by omega)⟩

/-- Corrected CCDN Proposition 4.3.4 in every degree at least five: the surface bound
`C d^18 B` for integer equations in three variables with absolutely irreducible top-degree
form. -/
theorem affine_surface_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  obtain ⟨Cbig, hCbig, hbig⟩ := affine_surface_count_large_degree
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    top_form_surface_bounded_degree_linear_bound topFormSurfaceThreshold
  refine ⟨Cbig + Csmall, by positivity, fun f hir hd B hB => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ f.totalDegree by omega))
  by_cases hlarge : topFormSurfaceThreshold ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · calc
      _ ≤ Csmall * B := hsmall f hir hd (by omega) B hB
      _ ≤ (Cbig + Csmall) * 1 * B := by gcongr; linarith
      _ ≤ (Cbig + Csmall) * (f.totalDegree : ℝ) ^ 18 * B := by gcongr

end
end CCDN
