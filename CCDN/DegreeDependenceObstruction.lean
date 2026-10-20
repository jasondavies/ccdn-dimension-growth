module

public import CCDN.GridHypersurfaceLowerBound
public import CCDN.DegreeDependenceNumerics
public import CCDN.PolynomialPredicates

/-! Obstructions to improving the degree factors in dimension growth.
The lower bounds here come from explicitly constructed hypersurfaces with
absolutely irreducible top forms, so the affine examples meet the hypothesis
of CCDN Theorem 4. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Filter Asymptotics

theorem affine_hypersurface_factor_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {g : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ f : MvPolynomial (Fin n) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * g f.totalDegree * B ^ (n - 2))
    (d : ℕ) (hd : 5 ≤ d) :
    (d : ℝ) ^ 2 / 64 ≤ C * g d := by
  obtain ⟨f, B, hB, _, _, hdeg, htop, _, hlo, _⟩ :=
    exists_topform_hypersurface_lower_bounds d n (by omega) hn
  have hu := hbound f htop (by omega) B (by exact_mod_cast hB)
  rw [hdeg] at hu
  have hpos : (0 : ℝ) < (B : ℝ) ^ (n - 2) := by
    have : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    positivity
  exact (mul_le_mul_iff_left₀ hpos).mp (hlo.trans hu)

theorem affine_hypersurface_factor_not_isLittleO {n : ℕ} (hn : 3 ≤ n)
    {g : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ f : MvPolynomial (Fin n) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * g f.totalDegree * B ^ (n - 2)) :
    ¬ g =o[atTop] (fun d : ℕ => (d : ℝ) ^ 2) := by
  apply not_isLittleO_of_eventually_lower_bound (c := 1 / 64) (by norm_num) hC
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  · filter_upwards [eventually_ge_atTop 5] with d hd
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      affine_hypersurface_factor_lower_bound hn hbound d hd

private theorem projective_hypersurface_factor_lower_bound_three {n : ℕ} (hn : 3 ≤ n)
    {g : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ F : MvPolynomial (Fin (n + 1)) ℚ,
      F.IsHomogeneous F.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      5 ≤ F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * g F.totalDegree * B ^ (n - 1))
    (d : ℕ) (hd : 5 ≤ d) :
    (d : ℝ) / 8 ≤ C * g d := by
  obtain ⟨f, B, hB, _, _, hdeg, htop, hir, _, hlo⟩ :=
    exists_topform_hypersurface_lower_bounds d n (by omega) hn
  have hQdeg := (integer_absolute_top_rational_model f hdeg htop).1
  obtain ⟨hhom, hFdeg, hFir⟩ :=
    projective_closure_absolute_irreducible (map (Int.castRingHom ℚ) f) hQdeg hir
  have hhom' :
      (boundedHomogenize d (map (Int.castRingHom ℚ) f)).IsHomogeneous
        (boundedHomogenize d (map (Int.castRingHom ℚ) f)).totalDegree := by
    rwa [hFdeg]
  have hu := hbound _ hhom' hFir (by omega) B (by exact_mod_cast hB)
  rw [hFdeg] at hu
  have hpos : (0 : ℝ) < (B : ℝ) ^ (n - 1) := by
    have : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    positivity
  exact (mul_le_mul_iff_left₀ hpos).mp (hlo.trans hu)

theorem projective_hypersurface_factor_lower_bound {n : ℕ} (hn : 2 ≤ n)
    {g : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ F : MvPolynomial (Fin (n + 1)) ℚ,
      F.IsHomogeneous F.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      5 ≤ F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * g F.totalDegree * B ^ (n - 1))
    (d : ℕ) (hd : 5 ≤ d) :
    (d : ℝ) / 8 ≤ C * g d := by
  by_cases hn3 : 3 ≤ n
  · exact projective_hypersurface_factor_lower_bound_three hn3 hbound d hd
  have hn2 : n = 2 := by omega
  subst n
  obtain ⟨F, hhom, hdeg, hir, hgrid⟩ := exists_projective_grid_lower_bound d (by omega)
  let B := (d - 1) / 2 - (d - 1) / 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBd : B ≤ d := by dsimp [B]; omega
  have hu := hbound F (by rwa [hdeg]) hir (by omega) B (by exact_mod_cast hB)
  rw [hdeg] at hu
  norm_num only [Nat.reduceSub, pow_one] at hu
  have hds : d ≤ 2 * ((d - 1) / 2 + 1) := by omega
  have hdsR : (d : ℝ) ≤ 2 * (((d - 1) / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hds
  have hsquare : (d : ℝ) ^ 2 / 4 ≤ (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg d) hdsR 2
    nlinarith
  have hBdR : (B : ℝ) ≤ d := by exact_mod_cast hBd
  have hlo : ((d : ℝ) / 8) * B ≤ (projectiveCount (projectiveZeroLocus F) B : ℝ) := by
    calc
      _ ≤ (d : ℝ) ^ 2 / 4 := by
        nlinarith [mul_le_mul_of_nonneg_left hBdR (Nat.cast_nonneg d)]
      _ ≤ (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := hsquare
      _ ≤ _ := by exact_mod_cast hgrid
  have hpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  exact (mul_le_mul_iff_left₀ hpos).mp (hlo.trans hu)

theorem projective_hypersurface_factor_not_isLittleO {n : ℕ} (hn : 2 ≤ n)
    {g : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ F : MvPolynomial (Fin (n + 1)) ℚ,
      F.IsHomogeneous F.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      5 ≤ F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * g F.totalDegree * B ^ (n - 1)) :
    ¬ g =o[atTop] (fun d : ℕ => (d : ℝ)) := by
  apply not_isLittleO_of_eventually_lower_bound (c := 1 / 8) (by norm_num) hC
  · filter_upwards [eventually_ge_atTop 1] with d hd
    exact_mod_cast (show 0 < d by omega)
  · filter_upwards [eventually_ge_atTop 5] with d hd
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      projective_hypersurface_factor_lower_bound hn hbound d hd

/-- Any power of the degree in the uniform affine hypersurface estimate
has exponent at least two. The examples satisfy absolute irreducibility of
the highest-degree homogeneous part. -/
theorem affine_hypersurface_degree_exponent_ge_two {n : ℕ} (hn : 3 ≤ n)
    {e C : ℝ} (hC : 0 < C)
    (hbound : ∀ f : MvPolynomial (Fin n) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ e * B ^ (n - 2)) :
    2 ≤ e := by
  by_contra h
  have hh := natCast_rpow_isLittleO_of_lt (lt_of_not_ge h)
  have hnlo := affine_hypersurface_factor_not_isLittleO hn
    (g := fun d => (d : ℝ) ^ e) hC hbound
  exact hnlo (by simpa only [Real.rpow_two] using hh)

/-- Already on absolutely irreducible hypersurfaces in P^n, n≥2, a
uniform dimension-growth degree exponent must be at least one. -/
theorem projective_hypersurface_degree_exponent_ge_one {n : ℕ} (hn : 2 ≤ n)
    {e C : ℝ} (hC : 0 < C)
    (hbound : ∀ F : MvPolynomial (Fin (n + 1)) ℚ,
      F.IsHomogeneous F.totalDegree →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) F) →
      5 ≤ F.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveZeroLocus F) B : ℝ) ≤
        C * (F.totalDegree : ℝ) ^ e * B ^ (n - 1)) :
    1 ≤ e := by
  by_contra h
  have hh := natCast_rpow_isLittleO_of_lt (lt_of_not_ge h)
  have hnlo := projective_hypersurface_factor_not_isLittleO hn
    (g := fun d => (d : ℝ) ^ e) hC hbound
  exact hnlo (by simpa only [Real.rpow_one] using hh)

end
end CCDN
