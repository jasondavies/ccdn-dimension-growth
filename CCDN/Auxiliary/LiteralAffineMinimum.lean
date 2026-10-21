/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PrimeScaledAffineMinimum
public import CCDN.Auxiliary.LiteralAffineBadPrimes
import CCDN.Algebra.UnscaledAffineMinimum
import CCDN.Auxiliary.LiteralScaledAuxiliary
import CCDN.Height.AffineHeightCutoff
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Height.HypersurfaceHeightTransfer
/-! Quantitative degree selection for the literal affine bad-prime branch.
The logarithmic branch can be selected separately at the existence level. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem literal_scaled_hypersurface_auxiliary_badPrime_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        ((Real.exp 1 * literalAffineBadPrimeFactor f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant n *
        (Real.exp 1 * A * (f.totalDegree : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
            ((f.totalDegree : ℝ) ^ 2 *
              literalAffineBadPrimeFactor f) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) /
              (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
                (1 / ((n + 1 : ℝ) * f.totalDegree *
                  (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (f.totalDegree : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
            (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) := by
  have hb := literalAffineBadPrimeFactor_nonneg f
  exact scaled_hypersurface_auxiliary_bound_of_badPrime_le f hf hd hp hA hB hBp
    (mul_nonneg (Real.exp_pos _).le hb) hb le_rfl

theorem literal_prime_scaled_affine_auxiliary_minimum {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f)
    (habs : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) (hp0 : ¬(p : ℤ) ∣ f.coeff 0)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (literalAffineBadPrimeFactor f) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := literalAffineBadPrimeFactor f
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB)))
    (sq_nonneg _)
  have hb : 0 ≤ b := literalAffineBadPrimeFactor_nonneg f
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases hmin : T ≤ (d : ℝ) ^ 2 * b
  · obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ := prime_scaled_affine_auxiliary_height f hprim hir hd
      hp hp0 hA hB hpB hBp
    refine ⟨g, hg0, hgnd, hgdeg.trans ?_, hgz⟩
    change affineLogarithmicAuxiliaryBound n d A B L ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold affineLogarithmicAuxiliaryBound affineMinimumAuxiliaryBound
    rw [min_eq_left hmin]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    apply add_le_add _ le_rfl
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) (by positivity)) hT) (by positivity)
  · obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ := literal_prime_scaled_affine_auxiliary f hprim habs hd
      hp hp0 hB hpB
    refine ⟨g, hg0, hgnd, (hgdeg.trans
      (literal_scaled_hypersurface_auxiliary_badPrime_bound f hir.ne_zero hd hp hA hB hBp)).trans ?_, hgz⟩
    change _ ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold affineMinimumAuxiliaryBound
    rw [min_eq_right (le_of_not_ge hmin)]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    apply add_le_add _ le_rfl
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0) (by positivity)) (by positivity))
        (by positivity)

lemma unscaled_auxiliary_bad_factor_bound {n k : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {b S B : ℝ} (hb : 0 ≤ b) (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k)
    (hmin : (f.totalDegree : ℝ) ^ 2 * b ≤
      Real.log (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) +
        f.totalDegree * Real.log B + (f.totalDegree : ℝ) ^ 2) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B b (integerCoefficientHeight f : ℝ) ≤
      affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) b := by
  let d := f.totalDegree
  let H := (integerCoefficientHeight f : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  let E := Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hd0 : (0 : ℝ) < d := by dsimp [d]; exact_mod_cast hd
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hLH : L ≤ H := leading_height_le_coefficient_height f
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)
  have hpower : B ^ α ≤ E * B ^ β := by
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      polynomial_box_projective_power_bound (r := n + 1) (by omega) hd hS hB hbound
  have hpow : L ^ q ≤ H ^ q := Real.rpow_le_rpow hL0.le hLH (by dsimp [q]; positivity)
  have hpowers : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) =
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 :=
    rpow_four_sub_eq_mul_sq hd0 n
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ α / H ^ q ≤
      K * E * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) * B ^ β / L ^ q := by
    calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * (E * B ^ β) / L ^ q := by
        apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow).trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity)
      _ = E * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) * B ^ β / L ^ q := by
        rw [hpowers]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hK1
          (show 0 ≤ E * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) * B ^ β / L ^ q by
            dsimp only [E]; positivity)
        simpa only [one_mul, mul_assoc, mul_div_assoc] using hh
  unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound
  rw [min_eq_right hmin]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le

/-- The literal-factor auxiliary in the complete minimum form on a box of
polynomial size in the degree. The better of two auxiliaries is chosen. -/
theorem literal_unscaled_affine_auxiliary_minimum {n k : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f)
    (habs : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (literalAffineBadPrimeFactor f) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := literalAffineBadPrimeFactor f
  let E := Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  by_cases hmin : T ≤ (d : ℝ) ^ 2 * b
  · obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ := unscaled_affine_auxiliary_minimum f hprim hir hd hS hB hbound
    refine ⟨g, hg0, hgnd, hgdeg.trans ?_, hgz⟩
    change affineMinimumAuxiliaryBound n d E B L _ ≤ affineMinimumAuxiliaryBound n d E B L b
    unfold affineMinimumAuxiliaryBound
    rw [min_eq_left hmin]
    have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
      (Real.exp_pos _).le.trans (le_max_right _ _)
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    gcongr
    exact min_le_left _ _
  · obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ := literal_unscaled_affine_auxiliary f hprim habs hd hB
    exact ⟨g, hg0, hgnd, hgdeg.trans (unscaled_auxiliary_bad_factor_bound f hir.ne_zero hd
      (literalAffineBadPrimeFactor_nonneg f) hS hB hbound (le_of_not_ge hmin)), hgz⟩

end
end CCDN
