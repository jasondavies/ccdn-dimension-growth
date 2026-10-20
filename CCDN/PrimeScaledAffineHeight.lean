module

public import CCDN.PrimeScaledAffineAuxiliary
public import CCDN.AffineScalingExponent
public import CCDN.ScalingPrime

/-! The coefficient-sensitive affine degree saving for a prime comparable
to the box radius. The leading homogeneous height belongs to the original equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def affineHeightTransferConstant (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)

def affineLogarithmicAuxiliaryBound (n d : ℕ) (A B L : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (affineHeightTransferConstant n * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        (Real.log L + d * Real.log B + (d : ℝ) ^ 2) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
          L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)))

theorem scaled_hypersurface_auxiliary_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℤ} (hp : 1 ≤ p) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree p f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree p f) : ℝ) ≤
      affineLogarithmicAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) := by
  let d := f.totalDegree
  let F := scaledHomogenize d p f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let Y := (p : ℝ) ^ d * L
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let K := affineHeightTransferConstant n
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hd0 : (0 : ℝ) < d := by dsimp only [d]; exact_mod_cast hd
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hL0 : 0 < L := by linarith
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hp1) hL
  have hYH : Y ≤ H := scaledHomogenize_leading_height_lower f hp
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d (by omega) hf
  have hFdegree : F.totalDegree = d := (scaledHomogenize_homogeneous p f le_rfl).totalDegree hF0
  have hK : 0 ≤ K := by
    dsimp only [K, affineHeightTransferConstant]
    exact mul_nonneg (by positivity) (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hlogY : Real.log Y = d * Real.log p + Real.log L := by
    dsimp only [Y]
    rw [Real.log_mul (by positivity) hL0.ne', Real.log_pow]
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg hd0.le (Real.log_nonneg hB))) (sq_nonneg _)
  have hnum : Real.log Y + (d : ℝ) ^ 2 ≤ T := by
    rw [hlogY]
    dsimp only [T]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpB) hd0.le
    linarith
  have hYpow : Y ^ q = (p : ℝ) ^ β * L ^ q := by
    simpa only [Nat.cast_add, Nat.cast_one] using scaled_height_rpow (r := n + 1) (by omega) hd hp0 hL0
  have htransfer : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor F / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) / ((p : ℝ) ^ β * L ^ q) := by
    have hh := hypersurface_badPrime_height_transfer F hF0 hFdegree hd hY hYH
    rw [hYpow] at hh
    exact hh
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hpower : B ^ α / (p : ℝ) ^ β ≤ A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, hnR] using
      affine_scaling_box_power (r := n + 1) (by omega) hd hB hA hp0 hBp
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor F * B ^ α / H ^ q ≤
      K * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) / L ^ q := by
    calc
      _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) * B ^ α /
          ((p : ℝ) ^ β * L ^ q) := by
        convert mul_le_mul_of_nonneg_right htransfer (show 0 ≤ B ^ α by positivity) using 1 <;> ring
      _ = K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
          ((Real.log Y + (d : ℝ) ^ 2) / L ^ q) * (B ^ α / (p : ℝ) ^ β) := by ring
      _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (T / L ^ q) *
          (A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
        · exact hpower
        · positivity
        · positivity
      _ = _ := by ring
  unfold hypersurfaceAuxiliaryDegreeBound affineLogarithmicAuxiliaryBound
  apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  exact add_le_add (add_le_add hmain le_rfl) le_rfl

/-- The logarithmic-height branch of the affine auxiliary bound, provided
an actual scaling prime lies between B/A and B and avoids the constant term.
The constructed polynomial vanishes on every original integer zero in the box. -/
theorem prime_scaled_affine_auxiliary_height {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineLogarithmicAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  obtain ⟨g, hg0, hgnd, hgdegree, hgzero⟩ := prime_scaled_affine_auxiliary f hprim hir hd hp hp0 hB hpB
  refine ⟨g, hg0, hgnd, hgdegree.trans ?_, hgzero⟩
  exact scaled_hypersurface_auxiliary_bound f hir.ne_zero hd
    (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) hA hB
    (by simpa only [Int.cast_natCast] using hpB) (by simpa only [Int.cast_natCast] using hBp)

/-- A small nonzero constant coefficient supplies the scaling prime itself.
No prime-choice hypothesis remains in this branch of Proposition 4.2.1. -/
theorem affine_auxiliary_of_small_constant_coefficient {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineLogarithmicAuxiliaryBound n f.totalDegree scalingPrimeRatio B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hc hheight
  exact prime_scaled_affine_auxiliary_height f hprim hir hd hp hnd
    scalingPrimeRatio_one_le (scalingPrimeRatio_one_le.trans hB) hhi hlo.le

end
end CCDN
