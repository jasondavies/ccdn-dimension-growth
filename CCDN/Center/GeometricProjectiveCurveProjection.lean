/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectivePermutation
public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.DegreePreservingProjectionBox
public import CCDN.Projection.ImageFractionField
import CCDN.Center.HomogeneousCurveHilbert
import CCDN.Center.ProjectiveIncidencePermutation
import CCDN.Hilbert.CoordinateIndependence
import CCDN.Projection.AffineProjectionCount
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Projection.ProjectiveProjectionCount
import CCDN.ForMathlib.MvPolynomial
import CCDN.Algebra.ReconstructionFunctionField
import CCDN.Projection.BoundedDegreePreservingProjection
import CCDN.Projection.DegreePreservingProjectionCount

/-!
The geometric projective-curve projection statement, uniformly for all
heights, obtained by choosing a proper coordinate chart. The coordinate
permutation has no height cost and is chosen before the radius.

An explicitly constructed geometrically integral plane curve has the
source degree and source function field of a projective curve, and satisfies
the additive point-count comparison of Propositions 4.3.1 and 4.3.2.

The constructed bounded plane projection of a geometrically integral
curve is geometrically integral, birational and degree-preserving. Its
point-count error is at most d(d-1).
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_geometrically_integral_curve_projection
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n : ℕ}
    [DecidableEq (Fin 2 → K)]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (d : ℕ) (hd : 0 < d)
    (hdegree : HasFilteredCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧
      let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
      IsBirationalImage I a f ∧ Irreducible (map (algebraMap K L) f) ∧ f.totalDegree = d ∧
      aeval a (pderiv 1 f) ∉ I ∧
      (∃ P : Fin n → MvPolynomial (Fin 2) K, ∀ i,
        (P i).totalDegree ≤ d ∧
        aeval a (pderiv 1 f) * X i - aeval a (P i) ∈ I) ∧
      ∀ S : Finset (Fin n → K), (∀ z ∈ S, z ∈ idealZeroLocus I) →
        S.card ≤ (S.image (fun z i => eval z (a i))).card + d * (d - 1) := by
  classical
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hu, hker⟩ :=
    exists_bounded_degree_preserving_projection I d hd hdegree
  let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
  have ha (i : Fin 2) : (a i).totalDegree ≤ 1 := by
    fin_cases i <;> exact momentCoordinate_degree _ _ _
  have hker' : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
    ext g
    rw [mem_projectionCoordinateMap_ker, Ideal.mem_span_singleton]
    exact hker g
  have hgeom := projection_equation_irreducible_map (L := L) I a f hf.ne_zero hker'
  obtain ⟨hQ, _, P, hP⟩ := degree_preserving_projection_reconstruction
    I a ha d hdegree hu f hf.ne_zero hfd hker
  refine ⟨k₀, k₁, f, hk₀, hk₁,
    ⟨reconstruction_generates_functionField I a (pderiv 1 f) P hQ (fun i => (hP i).2), hf, hker'⟩,
    hgeom, hfd, hQ, ⟨P, hP⟩, ?_⟩
  exact degree_preserving_projection_card_le I a ha d hdegree hu f hf.ne_zero hfd hker

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The projective curve clause of Proposition 4.3.2 on a proper standard
chart. The affine plane equation generates exactly the chart function field;
its projective closure stays irreducible after extending coefficients. -/
private theorem exists_geometric_projective_curve_count_reduction_of_chart
    {L : Type*} [Field L] [Algebra ℚ L] {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hX : X 0 ∉ I) (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) ℚ),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ f.totalDegree = d ∧
      IsBirationalImage (projectiveChartIdeal I)
        ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∧
      (scaledHomogenize d 1 f).IsHomogeneous d ∧
      Irreducible (scaledHomogenize d 1 f) ∧
      Irreducible (map (algebraMap ℚ L) (scaledHomogenize d 1 f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
          (projectionBoxFactor n d * B) + d ^ 2 := by
  let J := projectiveChartIdeal I
  let : (J.map (map (algebraMap ℚ L))).IsPrime :=
    projectiveChartIdeal_geometrically_prime I hX
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hP, hfL, hfd, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) J d hd
      (projectiveChartIdeal_degree I hX hdegree)
  refine ⟨k₀, k₁, f, hk₀, hk₁, hfd, hP, scaledHomogenize_homogeneous 1 f hfd.le, ?_, ?_, ?_⟩
  · simpa only [hfd] using scaledHomogenize_irreducible f hP.irreducible one_ne_zero
  · rw [scaledHomogenize_map, map_one]
    have hdeg : (map (algebraMap ℚ L) f).totalDegree = d :=
      (totalDegree_map_of_injective (algebraMap ℚ L).injective _).trans hfd
    simpa only [hdeg] using scaledHomogenize_irreducible _ hfL one_ne_zero
  · exact projective_curve_count_le_of_moment_projection I hX hd hdegree f hfd hk₀ hk₁
      hP.aeval_mem hcount

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_coordinate_not_mem_of_positive_hilbert_dimension
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

/-- A homogeneous prime of positive Hilbert dimension can be moved by a coordinate permutation
so that `X 0` is not in it, keeping it homogeneous and keeping its Hilbert polynomial. -/
theorem exists_projectivePermutedIdeal_chart {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] (hJ : IsHomogeneousIdeal J)
    (hdim : 0 < (filteredHilbertPolynomial J).natDegree) :
    ∃ e : Equiv.Perm (Fin (n + 1)), IsHomogeneousIdeal (projectivePermutedIdeal J e) ∧
      X 0 ∉ projectivePermutedIdeal J e ∧
      filteredHilbertPolynomial (projectivePermutedIdeal J e) = filteredHilbertPolynomial J := by
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem_of_positive_hilbert_dimension J hdim
  refine ⟨Equiv.swap 0 j, projectivePermutedIdeal_homogeneous J hJ _, ?_,
    projectivePermutedIdeal_filteredHilbertPolynomial J _⟩
  rw [mem_projectivePermutedIdeal, rename_X]
  simpa only [Equiv.swap_apply_left] using hj

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

private lemma projectionBoxFactor_le_degree_power (n : ℕ) {d : ℕ} (hd : 0 < d) :
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
      (scaledHomogenize d 1 f).IsHomogeneous d ∧
      (scaledHomogenize d 1 f).totalDegree = d ∧
      Irreducible (scaledHomogenize d 1 f) ∧
      Irreducible (map (algebraMap ℚ L) (scaledHomogenize d 1 f)) ∧
      ∀ B : ℝ, 1 ≤ B → projectiveCount (projectiveIdealZeroLocus I) B ≤
        projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
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
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hfd, hP, hhom, hF, hFL, hcount⟩ :=
    exists_geometric_projective_curve_count_reduction_of_chart (L := L) J hX hd hJ
  refine ⟨e, k₀, k₁, f, hX, hk₀, hk₁, hP.irreducible, hfd, hP.aeval_mem_iff, hP.birational,
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
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hP, hfL, hfd, _, _, hcount⟩ :=
    exists_geometrically_integral_curve_projection (L := L) I d hd hdegree
  refine ⟨k₀, k₁, f, hk₀, hk₁, hP.irreducible, hfL, hfd, hP.aeval_mem_iff, hP.birational, ?_⟩
  intro B hB
  apply (affine_curve_count_le_of_moment_projection I f hk₀ hk₁ hP.aeval_mem_iff hcount B
    hB).trans
  apply Nat.add_le_add
  · apply count_mono (Set.Subset.refl _)
    exact mul_le_mul_of_nonneg_right (projectionBoxFactor_le_degree_power n hd) (by linarith)
  · calc
      d * (d - 1) ≤ d * d := Nat.mul_le_mul_left d (Nat.sub_le _ _)
      _ = d ^ 2 := (sq d).symm

end
end CCDN
