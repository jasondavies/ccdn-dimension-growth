module

public import CCDN.HypersurfaceLargeHeightAuxiliary

/-! Combine the two height ranges under the paper's explicit leading-coefficient
position condition. The main term retains the original bad-prime factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma inverse_rpow_le_of_log_position {H L q D : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hq : 0 ≤ q) (hposition : Real.log H ≤ Real.log L + D) :
    1 / L ^ q ≤ Real.exp (q * D) / H ^ q := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div one_ne_zero (by positivity), Real.log_div (Real.exp_pos _).ne' (by positivity),
    Real.log_one, Real.log_exp, Real.log_rpow hL, Real.log_rpow hH]
  nlinarith [mul_le_mul_of_nonneg_left hposition hq]

lemma hypersurfaceSmallThreshold_position {n d : ℕ} {B H L A T : ℝ}
    (hd : 0 < d) (hB : 0 ≤ B) (hH : 0 < H) (hL : 0 < L) (hA : 0 ≤ A)
    (hposition : Real.log H ≤ Real.log L + T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) :
    hypersurfaceSmallThreshold n d B L A ≤
      Real.exp (T / (n + 1 : ℝ)) * hypersurfaceSmallThreshold n d B H A := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
  have hh := inverse_rpow_le_of_log_position hH hL
    (show 0 ≤ 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) by positivity) hposition
  have he : (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) *
      (T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) = T / (n + 1 : ℝ) := by field_simp
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * A *
        B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) by positivity)
  simpa only [hypersurfaceSmallThreshold, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hm

/-- Explicit constant for the positioned absolutely irreducible case. -/
def hypersurfacePositionedAuxiliaryConstant (n : ℕ) (T : ℝ) : ℝ :=
  4 + 8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) +
    Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))

/-- The coefficient-sensitive auxiliary theorem for an absolutely irreducible
homogeneous equation satisfying explicit leading-coefficient positioning, for any
finite prime set `bad` for which the normalized comparison holds. Both height ranges
and the degree are constructed. -/
theorem positioned_auxiliary_degree_of_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (T : ℝ) (hT : 0 ≤ T)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfacePositionedAuxiliaryConstant n T *
        auxDegreeBound n d B (primeSetFactor bad) H ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  let Q := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * primeSetFactor bad * B ^ boxExponent n d /
    H ^ heightExponent n d
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let C := hypersurfacePositionedAuxiliaryConstant n T
  let Cs := Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))
  let Cl := 8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) + 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD : 0 ≤ D := Real.rpow_nonneg hd0.le _
  have hlarge : 0 < Real.exp (hypersurfaceLargeHeightError (n + 1)
    (hypersurfaceNormalizedError n) T) := Real.exp_pos _
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
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hD1 : 1 ≤ D := hd1.trans hdD
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · have hlead : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ H := hcoeff (order.degree f)
    obtain ⟨M, hbound, hg⟩ := auxiliary_small_height_degree_of_comparison order f hf0 hd z hB
      hbox bad hcomp ((Real.log_le_log hL hlead).trans hsmall)
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
  · obtain ⟨M, hbound, hg⟩ := hypersurface_auxiliary_large_height_degree order f hf hd hir H hH
      hcoeff z hprim hz hB hbox T hT (le_of_not_ge hsmall) hposition
    refine ⟨M, ?_, hg⟩
    change (M : ℝ) ≤ C * (Q + l + D)
    change (M : ℝ) ≤ Cl * D at hbound
    have h1 := mul_le_mul_of_nonneg_right hCl hD
    have h2 := mul_nonneg (show 0 ≤ C by linarith) (add_nonneg hQ hl)
    nlinarith

end
end CCDN
