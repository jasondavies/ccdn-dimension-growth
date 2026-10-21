/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Projection.ProjectiveLinearCountTransfer
import CCDN.Projection.AffineProjectionCount
/-! Integral-point counts under an integer linear projection.
In the application, the finite-fiber hypothesis follows from normalization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def integerAffineLinearImage {m n : ℕ} (P : Fin m → Fin n → ℤ)
    (x : IntPoint n) : IntPoint m := fun i => ∑ j, P i j * x j

private lemma rationalPoint_integerAffineLinearImage {m n : ℕ}
    (P : Fin m → Fin n → ℤ) (x : IntPoint n) :
    rationalPoint (integerAffineLinearImage P x) =
      fun i => eval (rationalPoint x) (integerLinearForm (P i)) := by
  funext i
  simp [rationalPoint, integerAffineLinearImage, eval_linearForm]

theorem affine_integer_linear_count_transfer
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (P : Fin m → Fin n → ℤ) (f : MvPolynomial (Fin m) ℚ)
    (hrelation : aeval (fun i => integerLinearForm (P i)) f ∈ I)
    (M : ℕ)
    (hfinite : ∀ z : Fin m → ℚ, ∀ s : Finset (Fin n → ℚ),
      (∀ x ∈ s, x ∈ idealZeroLocus I) →
      (∀ x ∈ s, ∀ i, eval x (integerLinearForm (P i)) = z i) → s.card ≤ M)
    (H B : ℝ) (hH : 0 ≤ H) (hP : ∀ i j, |(P i j : ℝ)| ≤ H) :
    count (idealZeroLocus I) B ≤ M * count (zeroLocus f) ((n : ℝ) * H * B) := by
  classical
  let π := integerAffineLinearImage P
  let s := integralPoints (idealZeroLocus I) B
  let t := integralPoints (zeroLocus f) ((n : ℝ) * H * B)
  have himage : s.image π ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxB, hxI⟩ := mem_integralPoints.mp hx
    apply mem_integralPoints.mpr
    constructor
    · intro i
      change |((∑ j, P i j * x j : ℤ) : ℝ)| ≤ _
      rw [Int.cast_sum]
      calc
        _ ≤ ∑ j, |((P i j * x j : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin n, H * B := by
          apply Finset.sum_le_sum
          intro j _
          rw [Int.cast_mul, abs_mul]
          exact mul_le_mul (hP i j) (hxB j) (abs_nonneg _) hH
        _ = _ := by simp [mul_assoc]
    · change eval (rationalPoint (integerAffineLinearImage P x)) f = 0
      rw [rationalPoint_integerAffineLinearImage]
      have hz := hxI _ hrelation
      rwa [eval_polynomial_coordinate_map] at hz
  have hfiber (y : IntPoint m) : (s.filter (fun x => π x = y)).card ≤ M := by
    let u := s.filter (fun x => π x = y)
    have hcount := hfinite (rationalPoint y) (u.image rationalPoint)
    rw [Finset.card_image_of_injective u (rationalPoint_injective n)] at hcount
    apply hcount
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_integralPoints.mp (Finset.mem_filter.mp hw).1).2
    · intro x hx i
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have he := congrFun (rationalPoint_integerAffineLinearImage P w) i
      rw [show integerAffineLinearImage P w = y from (Finset.mem_filter.mp hw).2] at he
      exact he.symm
  change s.card ≤ M * t.card
  rw [Finset.card_eq_sum_card_image π s]
  calc
    _ ≤ ∑ _y ∈ s.image π, M := Finset.sum_le_sum (fun y _ => hfiber y)
    _ = M * (s.image π).card := by simp [Nat.mul_comm]
    _ ≤ M * t.card := Nat.mul_le_mul_left M (Finset.card_le_card himage)

end
end CCDN
