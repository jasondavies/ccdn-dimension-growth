/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.DegreePreservingProjectionBox
public import CCDN.Curve.Curve
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Projection.BoundedDegreePreservingProjection
/-! Reduce the integral-point count of an arbitrary prime affine curve
to the proved plane count, using the constructed degree-preserving projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma rationalPoint_injective (n : ℕ) : Function.Injective (@rationalPoint n) := by
  intro z w he
  funext j
  have hh := congrFun he j
  change (z j : ℚ) = (w j : ℚ) at hh
  exact_mod_cast hh

theorem affine_curve_count_le_of_moment_projection {n d k₀ k₁ : ℕ}
    (I : Ideal (CoordinatePolynomial n))
    (f : MvPolynomial (Fin 2) ℚ)
    (hk₀ : k₀ ≤ n ^ 2 * d) (hk₁ : k₁ ≤ n * d ^ 2)
    (hker : ∀ g, aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] g ∈ I ↔ f ∣ g)
    (hcount : ∀ S : Finset (Fin n → ℚ), (∀ z ∈ S, ∀ g ∈ I, eval z g = 0) →
      S.card ≤ (S.image (fun z i =>
        eval z (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i))).card + d * (d - 1))
    (B : ℝ) (hB : 1 ≤ B) :
    count (idealZeroLocus I) B ≤
      count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  classical
  let S := integralPoints (idealZeroLocus I) B
  let R := S.image rationalPoint
  let π : RatPoint n → RatPoint 2 := fun z =>
    ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
  let P := S.image (degreeProjection n k₀ k₁)
  have hR : ∀ z ∈ R, ∀ g ∈ I, eval z g = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact (mem_integralPoints.mp hz).2
  have hc := hcount R hR
  have hRcard : R.card = S.card := Finset.card_image_of_injective S (rationalPoint_injective n)
  have himg : R.image π = P.image rationalPoint := by
    simp only [R, P, Finset.image_image]
    congr 1
    funext z
    exact (rationalPoint_degreeProjection z).symm
  have hπ : (fun z i => eval z
      (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i)) = π := by
    funext z i
    fin_cases i <;> rfl
  rw [hπ, hRcard, himg, Finset.card_image_of_injective P (rationalPoint_injective 2)] at hc
  have hP : P ⊆ integralPoints (zeroLocus f) (projectionBoxFactor n d * B) := by
    rintro _ hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzbox := mem_integerBox.mpr (mem_integralPoints.mp hz).1
    apply mem_integralPoints.mpr
    refine ⟨mem_integerBox.mp (degreeProjection_box hk₀ hk₁ (by linarith) hzbox), ?_⟩
    change eval (rationalPoint (degreeProjection n k₀ k₁ z)) f = 0
    rw [rationalPoint_degreeProjection]
    have hfI := (hker f).mpr (dvd_refl f)
    have hh := (mem_integralPoints.mp hz).2 _ hfI
    rw [eval_polynomial_coordinate_map] at hh
    convert hh using 1
    congr 2
    funext j
    fin_cases j <;> rfl
  exact hc.trans (Nat.add_le_add_right (Finset.card_le_card hP) _)

/-- An integral affine curve of degree `d` has an irreducible plane equation `f` of degree
`d` such that, for every radius `B ≥ 1`, its integral points of height at most `B` number at
most those of `f` in a box enlarged by `projectionBoxFactor n d`, plus `d(d-1)`. -/
theorem exists_plane_count_reduction {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 2) ℚ, Irreducible f ∧ f.totalDegree = d ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hcount⟩ :=
    exists_bounded_projection_card_le I d hd hdegree
  have hπ : (fun z i => eval z (![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] i)) =
      fun z : Fin n → ℚ =>
        ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)] := by
    funext z i
    fin_cases i <;> rfl
  refine ⟨f, hf, hfd, affine_curve_count_le_of_moment_projection I f hk₀ hk₁ hker ?_⟩
  intro S hS
  rw [hπ]
  exact hcount S hS

end
end CCDN
