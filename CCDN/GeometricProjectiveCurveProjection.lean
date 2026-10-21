module

public import CCDN.GeometricCurveCountReduction
public import CCDN.HomogeneousCurveHilbert
public import CCDN.HilbertCoordinateIndependence
public import CCDN.ProjectivePermutation
public import CCDN.PolynomialPredicates

/-! The geometric projective-curve projection statement, uniformly for all
heights, obtained by choosing a proper coordinate chart. The coordinate
permutation has no height cost and is chosen before the radius. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_coordinate_not_mem_of_positive_hilbert_dimension
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hdim : 0 < (filteredHilbertPolynomial I).natDegree) :
    ∃ i : σ, X i ∉ I := by
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  obtain ⟨hne, _⟩ := Nat.card_pos_iff.mp (hU ▸ hdim)
  obtain ⟨i⟩ := hne
  refine ⟨i.val, ?_⟩
  intro hi
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have he : (X i : MvPolynomial U K) = 0 :=
    hAI.eq_zero_of_aeval_eq_zero (X i) (by simpa using hz)
  exact X_ne_zero i he

theorem projectivePermutedIdeal_geometrically_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (e : Equiv.Perm (Fin (n + 1))) :
    ((projectivePermutedIdeal I e).map (map (algebraMap K L))).IsPrime := by
  have he : projectivePermutedIdeal I e =
      RingHom.ker (projectionCoordinateMap I (X ∘ e)) := by
    ext f
    rw [mem_projectivePermutedIdeal, mem_projectionCoordinateMap_ker, rename_eq_aeval]
  rw [he]
  exact projection_kernel_geometrically_prime I _

def curveProjectionHeightConstant (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) ^ (2 * n)

lemma curveProjectionHeightConstant_pos (n : ℕ) : 0 < curveProjectionHeightConstant n := by
  unfold curveProjectionHeightConstant
  positivity

lemma projectionBoxFactor_le_degree_power (n : ℕ) {d : ℕ} (hd : 0 < d) :
    projectionBoxFactor n d ≤ curveProjectionHeightConstant n * (d : ℝ) ^ (2 * n) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold projectionBoxFactor curveProjectionHeightConstant
  rw [← pow_mul]
  calc
    _ ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * (2 * d)) ^ (2 * n) := by
      gcongr
      linarith
    _ = _ := by simp only [mul_pow]; ring

/-- Proposition 4.3.2 for curves, with a chart, birational map and
geometrically integral degree-d image constructed before the radius. -/
theorem exists_geometric_projective_curve_projection
    {L : Type*} [Field L] [Algebra ℚ L] {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (hd : 0 < d) (hdim : (filteredHilbertPolynomial I).natDegree = 2)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / 2) :
    ∃ (e : Equiv.Perm (Fin (n + 1))) (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      X 0 ∉ projectivePermutedIdeal I e ∧
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      let J := projectiveChartIdeal (projectivePermutedIdeal I e)
      let a := ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁]
      (∀ g, aeval a g ∈ J ↔ f ∣ g) ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (CoordinatePolynomial n ⧸ J)
          (FractionRing (CoordinatePolynomial n ⧸ J))
          ((Ideal.Quotient.mk J) (a i)))) = ⊤ ∧
      (boundedHomogenize d f).IsHomogeneous d ∧
      (boundedHomogenize d f).totalDegree = d ∧
      Irreducible (boundedHomogenize d f) ∧
      Irreducible (map (algebraMap ℚ L) (boundedHomogenize d f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (boundedHomogenize d f))
          (curveProjectionHeightConstant n * (d : ℝ) ^ (2 * n) * B) + d ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension I (by omega)
  let e := Equiv.swap (0 : Fin (n + 1)) j
  let J := projectivePermutedIdeal I e
  let : (J.map (map (algebraMap ℚ L))).IsPrime :=
    projectivePermutedIdeal_geometrically_prime I e
  have hX : X 0 ∉ J := by
    intro hx
    apply hj
    simpa only [rename_X, e, Equiv.swap_apply_left] using
      (mem_projectivePermutedIdeal I e (X 0)).mp hx
  have hJ : HasProjectiveCurveDegree J d := projectiveCurveDegree_permuted I e
    (projectiveCurveDegree_of_filteredHilbertPolynomial I hI d hdim hdegree)
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hfield, hhom, hF, hFL, hcount⟩ :=
    exists_geometric_projective_curve_count_reduction_of_chart (L := L) J hX hd hJ
  refine ⟨e, k₀, k₁, f, hX, hk₀, hk₁, hf, hfd, hker, hfield,
    hhom, hhom.totalDegree hF.ne_zero, hF, hFL, ?_⟩
  intro B hB
  apply (projectiveCount_le_permuted I e B).trans
  apply (hcount B hB).trans
  apply Nat.add_le_add_right
  apply projectiveCount_mono (Set.Subset.refl _)
  exact mul_le_mul_of_nonneg_right (projectionBoxFactor_le_degree_power n hd) (by linarith)

/-- The corresponding affine count has a dimension-only polynomial height
constant and the same explicit function-field identity. -/
theorem exists_geometric_affine_curve_projection
    {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧
      Irreducible (map (algebraMap ℚ L) f) ∧ f.totalDegree = d ∧
      let a := ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁]
      (∀ g, aeval a g ∈ I ↔ f ∣ g) ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (CoordinatePolynomial n ⧸ I)
          (FractionRing (CoordinatePolynomial n ⧸ I))
          ((Ideal.Quotient.mk I) (a i)))) = ⊤ ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (curveProjectionHeightConstant n * (d : ℝ) ^ (2 * n) * B) + d ^ 2 := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) I d hd hdegree
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfL, hfd, hker, hfield, ?_⟩
  intro B hB
  apply (affine_curve_count_le_of_moment_projection I f hk₀ hk₁ hker hcount B hB).trans
  apply Nat.add_le_add
  · apply count_mono (Set.Subset.refl _)
    exact mul_le_mul_of_nonneg_right (projectionBoxFactor_le_degree_power n hd) (by linarith)
  · calc
      d * (d - 1) ≤ d * d := Nat.mul_le_mul_left d (Nat.sub_le _ _)
      _ = d ^ 2 := (sq d).symm

end
end CCDN
