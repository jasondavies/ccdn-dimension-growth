module

public import CCDN.AffineChartAuxiliaryComparison
public import CCDN.HypersurfaceSmallHeightAuxiliary

/-! The small-height auxiliary construction with affine good reductions.
The coefficient saving and degree exponents agree with the projective
construction, while the finite excluded-prime set is supplied separately. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A degree above the proved threshold yields an integer homogeneous
nonmultiple vanishing at all supplied bounded primitive points. -/
theorem affine_chart_exists_auxiliary_small_height
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hM : 2 * d ≤ M)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 2 * d * (n + 2 : ℝ) * Real.log B)
    (hscale : (d : ℝ) * Real.log B ≤ (d : ℝ) ^ (1 / (n + 1 : ℝ)) * M)
    (hthreshold : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (Real.exp (∑ p ∈ bad, Real.log p / p)) < M) :
    ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
      (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hdM : d ≤ M := by omega
  by_contra hnone
  have hrel : ∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g := by
    intro g hg hv
    by_cases hg0 : g = 0
    · simp [hg0]
    · by_contra hnd
      exact hnone ⟨g, hg0, hg, hv, hnd⟩
  obtain ⟨s, _, hr, hc⟩ := affine_chart_no_auxiliary_comparison
    order f hf hd hdM hir z hprim hz bad hgood hB hbox hrel
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hlog := hypersurface_small_height_log_degree_bound (r := n + 1) (by omega) hd hM hr
    B |((order.leadingCoeff f : ℤ) : ℝ)| (Real.exp (∑ p ∈ bad, Real.log p / p))
    (hypersurfaceBadPrimeNormalizedError n) hB hL
    (by simpa only [Nat.cast_add, Nat.cast_one, hnR] using hheight)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hscale)
    (by simpa only [Nat.cast_add, Nat.cast_one, hnR, Real.log_exp] using hc)
  have hb := hypersurface_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith : 0 < B) (by linarith : 0 < |((order.leadingCoeff f : ℤ) : ℝ)|)
    (Real.exp_pos _) hlog
  have hb' : (M : ℝ) ≤ hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
      (Real.exp (∑ p ∈ bad, Real.log p / p)) := by
    simpa only [hypersurfaceSmallThreshold, Nat.cast_add, Nat.cast_one, hnR] using hb
  exact (not_lt_of_ge hb') hthreshold

/-- Construct an integer auxiliary degree for the supplied finite prime set.
The leading-coefficient saving and every radius exponent are retained. -/
theorem affine_chart_auxiliary_small_height_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 2 * d * (n + 2 : ℝ) * Real.log B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ 2 * d + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
          (Real.exp (∑ p ∈ bad, Real.log p / p)) + 2 ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  let R := hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
    (Real.exp (∑ p ∈ bad, Real.log p / p))
  have hR : 0 ≤ R := by dsimp only [R, hypersurfaceSmallThreshold]; positivity
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hdR.le _) (Real.log_nonneg hB)
  obtain ⟨M, hM, hscale, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (2 * d) hl hR
  refine ⟨M, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound
  · apply affine_chart_exists_auxiliary_small_height order f hf hd hM hir z hprim hz bad hgood hB hbox
      hheight _ hthreshold
    have hX : 0 < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
    dsimp only [l] at hscale
    rw [Real.rpow_sub hdR, Real.rpow_one] at hscale
    have hh := mul_le_mul_of_nonneg_right hscale hX.le
    have he : (d : ℝ) / (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Real.log B *
        (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d * Real.log B := by field_simp
    rw [he] at hh
    nlinarith

end
end CCDN
