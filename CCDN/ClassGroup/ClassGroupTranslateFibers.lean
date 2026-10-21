/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.OddDegreeNormCurves
public import CCDN.Plane.Plane
/-! Concrete integer-translation fibers of the bounded square-norm set
inject into integral points on the two signed norm curves. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

lemma bounded_infinite_places_norm_le (α : 𝓞 K) {B : ℝ}
    (hα : ∀ w : InfinitePlace K, w (α : K) ≤ B) :
    ((Algebra.norm ℤ α).natAbs : ℝ) ≤ B ^ Module.finrank ℚ K := by
  classical
  have he : (∏ w : InfinitePlace K, w (α : K) ^ mult w) =
      ((Algebra.norm ℤ α).natAbs : ℝ) := by
    rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
    norm_cast
    exact (Nat.cast_natAbs (Algebra.norm ℤ α)).symm
  rw [← he, ← sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro w _
    positivity
  · intro w _
    exact pow_le_pow_left₀ (apply_nonneg _ _) (hα w) _

lemma integer_translate_coordinate_le (α β : 𝓞 K) {B : ℝ}
    (hα : ∀ w : InfinitePlace K, w (α : K) ≤ B)
    (hβ : ∀ w : InfinitePlace K, w (β : K) ≤ B)
    {x : ℤ} (hx : α = algebraMap ℤ (𝓞 K) x - β) :
    |(x : ℝ)| ≤ 2 * B := by
  classical
  let w : InfinitePlace K := Classical.arbitrary _
  have hxK : (x : K) = (α : K) + (β : K) := by
    have h := congrArg (fun z : 𝓞 K ↦ (z : K)) hx
    simp only [map_sub, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply] at h
    change (α : K) = (x : K) - (β : K) at h
    exact (eq_sub_iff_add_eq.mp h).symm
  calc
    |(x : ℝ)| = w (x : K) := by
      rw [w.map_intCast, Int.norm_eq_abs]
    _ = w ((α : K) + (β : K)) := congrArg w hxK
    _ ≤ w (α : K) + w (β : K) := w.val.add_le _ _
    _ ≤ 2 * B := by linarith [hα w, hβ w]

def squareNormTranslateFiber (β : 𝓞 K) (B : ℝ) : Set (𝓞 K) :=
  {α | α ∈ boundedSquareNormIntegers K B ∧
    ∃ x : ℤ, α = algebraMap ℤ (𝓞 K) x - β}

lemma squareNormTranslateFiber_finite (β : 𝓞 K) (B : ℝ) :
    (squareNormTranslateFiber K β B).Finite :=
  (boundedSquareNormIntegers_finite K B).subset (fun _ h ↦ h.1)

def signedNormCurveLocus (β : 𝓞 K) (ε : ℤ) : Set (RatPoint 2) :=
  zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε))

theorem squareNormTranslateFiber_count_le (β : 𝓞 K) {B : ℝ}
    (hβ : ∀ w : InfinitePlace K, w (β : K) ≤ B) :
    (squareNormTranslateFiber K β B).ncard ≤
      count (signedNormCurveLocus K β 1) (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
      count (signedNormCurveLocus K β (-1))
        (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) := by
  classical
  let S := squareNormTranslateFiber K β B
  let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
  let Z := signedNormCurveLocus K β 1 ∪ signedNormCurveLocus K β (-1)
  let P := integralPoints Z H
  choose x hx using fun α : S ↦ α.property.2
  choose m hm using fun α : S ↦ α.property.1.2.2
  have hpoint (α : S) : ![(m α : ℤ), x α] ∈ P := by
    apply mem_integralPoints.mpr
    constructor
    · intro i
      fin_cases i
      · have hsq : (m α : ℝ) ^ 2 ≤ B ^ Module.finrank ℚ K := by
          rw [← Nat.cast_pow, ← hm α]
          exact bounded_infinite_places_norm_le K α α.property.1.2.1
        have hh := Real.le_sqrt_of_sq_le hsq
        change |((m α : ℤ) : ℝ)| ≤ H
        simp only [Int.cast_natCast]
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (m α : ℝ) by positivity)]
        exact hh.trans (le_max_right (2 * B) _)
      · exact (integer_translate_coordinate_le K α β α.property.1.2.1 hβ (hx α)).trans
          (le_max_left _ _)
    · have hnorm : (Algebra.norm ℤ
          (algebraMap ℤ (𝓞 K) (x α) - β)).natAbs = m α ^ 2 := by
        rw [← hx α]
        exact hm α
      rcases square_norm_yields_signedNormCurve_point K β (x α) (m α) hnorm with h | h
      · left
        have hc := congrArg (Int.castRingHom ℚ) h
        rw [MvPolynomial.map_eval, map_zero] at hc
        exact hc
      · right
        have hc := congrArg (Int.castRingHom ℚ) h
        rw [MvPolynomial.map_eval, map_zero] at hc
        exact hc
  let ι : S → P := fun α ↦ ⟨![(m α : ℤ), x α], hpoint α⟩
  have hi : Function.Injective ι := by
    intro α γ he
    have h := congrArg (fun p : P ↦ p.val 1) he
    change x α = x γ at h
    apply Subtype.ext
    rw [hx α, hx γ, h]
  have hcard : S.ncard ≤ count Z H := by
    have h := Nat.card_le_card_of_injective ι hi
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_coe, count, P] using h
  exact hcard.trans (count_union_le _ _ _)

end
end CCDN
