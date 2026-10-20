module

public import CCDN.AffineChartSmallAuxiliary
public import CCDN.HypersurfacePositionedAuxiliary

/-! Combine the two coefficient-height ranges for an affine-chart prime set.
The large-height branch remains the unconditional existing construction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient-sensitive auxiliary theorem for an absolutely irreducible
homogeneous equation satisfying explicit leading-coefficient positioning.
The integer degree is constructed in both height ranges for the given
affine-chart good-prime set. -/
theorem affine_chart_positioned_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (T : ℝ) (hT : 0 ≤ T)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfacePositionedAuxiliaryConstant n T *
        ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Real.exp (∑ p ∈ bad, Real.log p / p) *
            B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
              H ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  let Q := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * Real.exp (∑ p ∈ bad, Real.log p / p) *
    B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
      H ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))))
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let C := hypersurfacePositionedAuxiliaryConstant n T
  let Cs := Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))
  let Cl := 8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) + 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD : 0 ≤ D := Real.rpow_nonneg hd0.le _
  have hlarge : 0 < Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) := Real.exp_pos _
  have hsmallC : 0 < Cs := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC4 : 4 ≤ C := by
    dsimp only [C, hypersurfacePositionedAuxiliaryConstant]
    dsimp only [Cs] at hsmallC
    linarith
  have hCs : Cs ≤ C := by
    dsimp only [Cs, C, hypersurfacePositionedAuxiliaryConstant]
    linarith
  have hCl : Cl ≤ C := by
    dsimp only [Cl, C, hypersurfacePositionedAuxiliaryConstant]
    dsimp only [Cs] at hsmallC
    linarith
  have hexp : (1 : ℝ) ≤ 4 - 1 / (n + 1 : ℝ) := by
    have hh := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
      (show 1 ≤ (n + 1 : ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hdD : (d : ℝ) ≤ D := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 hexp
  have hD1 : 1 ≤ D := hd1.trans hdD
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · have hlead : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ H := hcoeff (order.degree f)
    obtain ⟨M, hbound, hg⟩ := affine_chart_auxiliary_small_height_degree order f hf hd hir
      z hprim hz bad hgood hB hbox ((Real.log_le_log hL hlead).trans hsmall)
    have hp := hypersurfaceSmallThreshold_position hd (by linarith : 0 ≤ B)
      (by linarith : 0 < H) hL (Real.exp_pos (∑ p ∈ bad, Real.log p / p)).le hposition
    have hp' : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
        (Real.exp (∑ p ∈ bad, Real.log p / p)) ≤ Cs * Q := by
      convert hp using 1
      unfold hypersurfaceSmallThreshold Cs Q
      ring
    refine ⟨M, ?_, hg⟩
    change (M : ℝ) ≤ C * (Q + l + D)
    change (M : ℝ) ≤ 2 * d + l + _ + 2 at hbound
    have h1 := mul_le_mul_of_nonneg_right hCs hQ
    have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith) hl
    have h3 := mul_le_mul_of_nonneg_right hC4 hD
    nlinarith
  · obtain ⟨M, hbound, hg⟩ := hypersurface_auxiliary_large_height_degree order f hf hd hir H hH hcoeff
      z hprim hz hB hbox T hT (le_of_not_ge hsmall) hposition
    refine ⟨M, ?_, hg⟩
    change (M : ℝ) ≤ C * (Q + l + D)
    change (M : ℝ) ≤ Cl * D at hbound
    have h1 := mul_le_mul_of_nonneg_right hCl hD
    have h2 := mul_nonneg (show 0 ≤ C by linarith) (add_nonneg hQ hl)
    nlinarith

end
end CCDN
