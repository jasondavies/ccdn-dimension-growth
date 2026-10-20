module

public import CCDN.ProjectiveVarietyDimensionGrowth
public import CCDN.ProjectiveHilbertCurveGrowth
public import CCDN.ProperHilbertDimension
public import CCDN.ZeroDimensionalProjectiveCount
public import CCDN.EmptyProjectiveHilbertDimension
public import CCDN.PolynomialPredicates

/-! CCDN Theorem 1 in the homogeneous-coordinate-ideal formulation: uniform projective
dimension growth for every rational prime projective variety of degree at least five.
The Hilbert polynomial determines the degree and dimension. Zero-dimensional and empty
loci are included.

The bound is assembled once, in `projectiveGrowth_of_le`, for any degree exponent which
dominates the exponents of the zero-dimensional count, the curve bound and the projection
bound. The exponent `2n² + 4n + 11` and the exponent `2n³` both follow. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN Theorem 1 in `ℙⁿ` with degree exponent `E`. A homogeneous prime ideal whose
Hilbert polynomial has degree `r` and leading coefficient `d / r!`, with `d ≥ 5`, has at
most `C d^E B^(r-1)` rational points of height at most `B`. The constant depends only on
`n` and `E`. -/
def ProjectiveGrowth (n E : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime → IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ E * B ^ ((filteredHilbertPolynomial I).natDegree - 1)

theorem ProjectiveGrowth.mono {n E E' : ℕ} (h : ProjectiveGrowth n E) (hE : E ≤ E') :
    ProjectiveGrowth n E' := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun I hprime hI d hd hdegree B hB =>
    (hbound I hprime hI d hd hdegree B hB).trans ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  gcongr

/-- In `ℙⁿ` with `n = m + k + 1`, the projection exponent has the closed form
`2mn + 5m + 3n + 21`. It is largest for `k = 1`, where it equals `2n² + 4n + 11`. -/
lemma projectiveProjectionDegreeExponent_le {m k n : ℕ} (h : m + k + 1 = n) (hk : 1 ≤ k) :
    projectiveProjectionDegreeExponent m k ≤ 2 * n ^ 2 + 4 * n + 11 := by
  subst h
  unfold projectiveProjectionDegreeExponent
  nlinarith

lemma point_exponent_le_cubic {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ 2 * n ^ 3 := by
  have := Nat.le_self_pow (by norm_num : 3 ≠ 0) n
  omega

lemma curve_exponent_le_cubic {n : ℕ} (hn : 2 ≤ n) : 3 * (n + 1) + 4 ≤ 2 * n ^ 3 := by
  nlinarith [Nat.mul_le_mul_left n (Nat.pow_le_pow_left hn 2)]

lemma quadratic_exponent_le_cubic {n : ℕ} (hn : 3 ≤ n) :
    2 * n ^ 2 + 4 * n + 11 ≤ 2 * n ^ 3 := by
  nlinarith

/-- Theorem 1 holds with any degree exponent `E` which dominates the exponent `n + 1` of the
zero-dimensional count, the exponent `3(n+1) + 4` of the curve bound and the exponent of
the projection bound in every dimension at least two. -/
theorem projectiveGrowth_of_le {n E : ℕ} (hpoint : 1 ≤ n → n + 1 ≤ E)
    (hcurve : 2 ≤ n → 3 * (n + 1) + 4 ≤ E)
    (hproj : ∀ m k, m + k + 1 = n → 1 ≤ m → 1 ≤ k →
      projectiveProjectionDegreeExponent m k ≤ E) :
    ProjectiveGrowth n E := by
  classical
  have hlt (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (hI : I.IsPrime) (d : ℕ) (hd : 5 ≤ d)
      (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
      (filteredHilbertPolynomial I).natDegree < n + 1 := by
    simpa only [Fintype.card_fin] using
      hilbert_dimension_lt_ambient_of_degree_gt_one I hI.ne_top d (by omega) hdegree
  have hempty (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
      (h : (filteredHilbertPolynomial I).natDegree = 0) (B : ℝ) :
      projectiveCount (projectiveIdealZeroLocus I) B = 0 := by
    rw [projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero I h]
    simp [projectiveCount, projectivePoints]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun I hprime _ d hd hdegree B _ => ?_⟩
    rw [hempty I (by have := hlt I hprime d hd hdegree; omega), Nat.cast_zero]
    positivity
  choose Cp _ hp using projective_variety_dimension_growth
  obtain ⟨T, hT⟩ := (((Set.finite_Iic n).prod (Set.finite_Iic n)).image
    fun p : ℕ × ℕ => Cp p.1 p.2).bddAbove
  obtain ⟨Cc, hCc, hc⟩ := projective_hilbert_curve_dimension_growth n hn
  let K : ℝ := max T 0 + Cc + 1
  have hTK : max T 0 + 1 ≤ K := by dsimp only [K]; linarith
  have hCK : Cc ≤ K := by dsimp only [K]; linarith [le_max_right T 0]
  refine ⟨K, by positivity, fun I hprime hI d hd hdegree B hB => ?_⟩
  let : I.IsPrime := hprime
  -- Each dimension gives a bound with a constant at most `K` and an exponent at most `E`.
  suffices h : ∃ C : ℝ, C ≤ K ∧ ∃ e ≤ E,
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ e * B ^ ((filteredHilbertPolynomial I).natDegree - 1) by
    obtain ⟨C, hC, e, he, h⟩ := h
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd1 he) (by positivity))
  have hdim := hlt I hprime d hd hdegree
  obtain h0 | h1 | h2 | h3 : (filteredHilbertPolynomial I).natDegree = 0 ∨
      (filteredHilbertPolynomial I).natDegree = 1 ∨
      (filteredHilbertPolynomial I).natDegree = 2 ∨
      3 ≤ (filteredHilbertPolynomial I).natDegree := by omega
  · refine ⟨0, by positivity, 0, Nat.zero_le _, ?_⟩
    rw [hempty I h0, Nat.cast_zero, zero_mul, zero_mul]
  · refine ⟨1, by linarith [le_max_right T 0], n + 1, hpoint hn, ?_⟩
    have hbound := zero_dimensional_projective_count_le I d h1 (by
      simpa only [h1, Nat.factorial_one, Nat.cast_one, div_one] using hdegree) B
    rw [h1, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact_mod_cast hbound
  · refine ⟨Cc, hCK, 3 * (n + 1) + 4, hcurve (by omega), ?_⟩
    rw [h2, show 2 - 1 = 1 from rfl, pow_one]
    exact hc I hprime hI d hd h2
      (by simpa only [h2, Nat.factorial_two, Nat.cast_ofNat] using hdegree) B hB
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h3
    obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k + 1 := ⟨n - m - 2, by omega⟩
    have hmk : Cp (m + 1) k ≤ T := hT (Set.mem_image_of_mem (fun p : ℕ × ℕ => Cp p.1 p.2)
      (show (m + 1, k) ∈ Set.Iic _ ×ˢ Set.Iic _ from
        ⟨Set.mem_Iic.mpr (by omega), Set.mem_Iic.mpr (by omega)⟩))
    refine ⟨Cp (m + 1) k, by linarith [le_max_left T 0], _,
      hproj (m + 1) k rfl (by omega) (by omega), ?_⟩
    rw [hm]
    exact hp (m + 1) k I hprime hI d hd hm (by simpa only [hm] using hdegree) B hB

/-- CCDN Theorem 1 with the degree exponent `2n² + 4n + 11` in every ambient projective
dimension `n`. -/
theorem projective_dimension_growth_explicit (n : ℕ) :
    ProjectiveGrowth n (2 * n ^ 2 + 4 * n + 11) :=
  projectiveGrowth_of_le (fun _ => by nlinarith) (fun _ => by nlinarith)
    fun _ _ h _ hk => projectiveProjectionDegreeExponent_le h hk

/-- CCDN Theorem 1 with the degree exponent `2n³` in every ambient projective dimension `n`,
including the zero-dimensional and empty cases. -/
theorem projective_dimension_growth_cubic (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d →
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (2 * n ^ 3) *
          B ^ ((filteredHilbertPolynomial I).natDegree - 1) :=
  projectiveGrowth_of_le point_exponent_le_cubic curve_exponent_le_cubic
    fun _ _ h _ hk => (projectiveProjectionDegreeExponent_le h hk).trans
      (quadratic_exponent_le_cubic (by omega))

end
end CCDN
