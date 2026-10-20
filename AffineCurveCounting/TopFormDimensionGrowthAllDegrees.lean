module

public import AffineCurveCounting.TopFormSurfaceFixedDegree
public import AffineCurveCounting.TopFormSurfaceCount
public import AffineCurveCounting.BoundedHyperplaneDimensionGrowth

/-! Full affine hypersurface dimension growth in degrees at least five.
The finitely many small surface degrees are absorbed in one constant;
the generic bounded-hyperplane induction then handles all dimensions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem top_form_surface_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  classical
  obtain ⟨Cbig, hCbig, hbig⟩ := top_form_surface_count
  have hsmall (i : Fin 11) := top_form_surface_fixed_degree_linear_bound (i.val + 5) (by omega)
  choose Csmall hCsmall hsmall using hsmall
  let C := Cbig + ∑ i : Fin 11, Csmall i
  have hsum : 0 ≤ ∑ i : Fin 11, Csmall i :=
    Finset.sum_nonneg (fun i _ => (hCsmall i).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB
  have hB0 : 0 ≤ B := by linarith
  by_cases hlarge : 16 ≤ f.totalDegree
  · apply (hbig f hir hlarge B hB).trans
    gcongr
    dsimp only [C]
    linarith
  · let i : Fin 11 := ⟨f.totalDegree - 5, by omega⟩
    have hdegree : f.totalDegree = i.val + 5 := by dsimp only [i]; omega
    have hh := hsmall i f hir hdegree B hB
    have hCi : Csmall i ≤ C := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 11))) =>
        (hCsmall j).le) (Finset.mem_univ i)
      dsimp only [C]
      linarith
    have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast (show 1 ≤ f.totalDegree by omega)
    have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 := one_le_pow₀ hdR
    calc
      _ ≤ Csmall i * B := hh
      _ ≤ C * B := mul_le_mul_of_nonneg_right hCi hB0
      _ ≤ C * (f.totalDegree : ℝ) ^ 18 * B := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdpow hC.le) hB0

/-- CCDN Theorem 4 for integer equations in all affine ambient dimensions
at least three. The constant depends only on dimension, and the explicit
degree exponent is 18 + 9n in n+3 variables. -/
theorem top_form_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin (n + 3)) ℤ,
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
        (homogeneousComponent f.totalDegree f)) →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ (18 + 9 * n) * B ^ (n + 1) := by
  rw [show n + 3 = 3 + n by omega]
  exact top_form_hypersurface_count_of_surface_bound 5 18 (by norm_num)
    top_form_surface_dimension_growth n

end
end AffineCurveCounting
