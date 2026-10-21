/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Algebra.ConjugatePrimeGridBound
public import CCDN.Curve.Curve
public import CCDN.Height.ProjectiveBox
import CCDN.Height.ProjectivePrimitive
import CCDN.Hypersurface.NonRationalVarietyCount
/-! Projective cone forms of CCDN 4.1.3 and 4.1.4. Primitive integer
representatives inject into the affine cone with the same radius. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Rational projective points annihilating an ideal with extension-field
coefficients. For a homogeneous ideal this is its rational projective locus. -/
def rationalProjectiveIdealZeroLocusOver
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) : Set (ProjectivePoint n) :=
  {x | ∀ (v : Fin (n + 1) → ℚ) (hv : v ≠ 0),
    Projectivization.mk ℚ v hv = x →
      (algebraMap ℚ K ∘ v) ∈ idealZeroLocus I}

theorem projective_ideal_count_le_affine_cone_count
    {n : ℕ} (I : Ideal (CoordinatePolynomial (n + 1))) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤ count (idealZeroLocus I) B := by
  classical
  let S := projectivePoints (projectiveIdealZeroLocus I) B
  have hsub : S.image primitiveProjectiveRep ⊆ integralPoints (idealZeroLocus I) B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hheight, hzero⟩ := mem_projectivePoints.mp hx
    apply mem_integralPoints.mpr
    refine ⟨fun i => (primitiveProjectiveRep_bound x i).trans hheight, ?_⟩
    exact hzero (rationalPoint (primitiveProjectiveRep x))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x))
      (primitiveProjectiveRep_mk x)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S primitiveProjectiveRep_injective] at hc
  exact hc

theorem extension_projective_ideal_count_le_affine_cone_count
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (B : ℝ) :
    projectiveCount (rationalProjectiveIdealZeroLocusOver I) B ≤
      count (rationalIdealZeroLocusOver I) B := by
  classical
  let S := projectivePoints (rationalProjectiveIdealZeroLocusOver I) B
  have hsub : S.image primitiveProjectiveRep ⊆
      integralPoints (rationalIdealZeroLocusOver I) B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hheight, hzero⟩ := mem_projectivePoints.mp hx
    apply mem_integralPoints.mpr
    refine ⟨fun i => (primitiveProjectiveRep_bound x i).trans hheight, ?_⟩
    exact hzero (rationalPoint (primitiveProjectiveRep x))
      (rationalPoint_ne_zero (primitiveProjectiveRep_ne_zero x))
      (primitiveProjectiveRep_mk x)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S primitiveProjectiveRep_injective] at hc
  exact hc

theorem non_rational_projective_count_le_box
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (hundef : ¬ ∃ J : Ideal (CoordinatePolynomial (n + 1)),
      J.map (map (algebraMap ℚ K)) = I)
    {B : ℝ} (hB : 0 ≤ B) :
    (projectiveCount (rationalProjectiveIdealZeroLocusOver I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (2 * B + 1) ^ m :=
  (Nat.cast_le.mpr (extension_projective_ideal_count_le_affine_cone_count I B)).trans
    (non_rational_prime_count_le_box I d hdimdeg hundef hB)

theorem nonabsolute_projective_variety_count_le_box
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] [IsGalois ℚ K]
    {n m : ℕ} (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (hred : ¬ (I.map (map (algebraMap ℚ K))).IsPrime)
    {B : ℝ} (hB : 0 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (2 * B + 1) ^ m :=
  (Nat.cast_le.mpr (projective_ideal_count_le_affine_cone_count I B)).trans
    (nonabsolute_variety_count_le_box I d hdimdeg hred hB)

end
end CCDN
