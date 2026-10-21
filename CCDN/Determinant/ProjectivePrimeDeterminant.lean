/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.PrimeAggregation
public import CCDN.Determinant.ProjectiveMultiplicity
/-! Sharp prime-power and global prime-sum bounds for projective plane
evaluation matrices. The excluded-prime set is explicit. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

theorem projectivePlaneTotalMultiplicity_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : 27 * (d : ℝ) ^ 4 < p) :
    (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      p + 165 * (d : ℝ) ^ 2 * Real.sqrt p := by
  have hp : 27 * d ^ 4 < p := by exact_mod_cast hsize
  have hchar : d < p := by
    have h1 := Nat.le_mul_self d
    have h2 := Nat.le_mul_self (d * d)
    nlinarith only [hp, h1, h2]
  have hmass := projectivePlaneTotalMultiplicity_le_card_add_correction f hf hd hir hchar
  have hmassR : (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectivePlaneResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) := by
    exact_mod_cast hmass
  have hc := projective_plane_finite_field_card_bound f hf hd hir hsize
  have hcorr := singular_correction_absorb (show 0 < d by omega)
    (L := 27 * (d : ℝ) ^ 4)
    (show (d : ℝ) ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith [sq_nonneg ((d : ℝ) ^ 2)])
    hsize
  push_cast at hmassR hcorr
  nlinarith

/-- A uniform local exponent at primes `p > 27*d^4` of irreducible reduction. -/
theorem projective_plane_minorGcd_dvd {s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : 27 * (d : ℝ) ^ 4 < p)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * (p + 165 * (d : ℝ) ^ 2 * Real.sqrt p)) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  obtain ⟨hpos, e, _, he, hdiv⟩ := projective_reduction_minorGcd hs f hf hir.ne_zero
    F hF z hprim hz
  have hm := projectivePlaneTotalMultiplicity_le f hf hd hir hsize
  refine ⟨e, ?_, hdiv⟩
  apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

theorem projective_determinant_log_lower_at_rank {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad,
      27 * (d : ℝ) ^ 4 < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      (∑ p ∈ bad, Real.log p / p) - degreeFourDeterminantError 164) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := determinant_log_lower_of_local_divisors_degree_four (x := (s : ℝ))
    (by exact_mod_cast hs) (show 0 < d by omega) (show (0 : ℝ) ≤ 165 by norm_num)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) bad ∅ (empty_subset bad)
    (by simp) 0 (lt_of_lt_of_le one_pos (Int.Matrix.one_le_minorGcd hrows)) (by
      rw [Nat.floor_natCast]
      intro p hp hcut
      have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
      simpa only [div_div] using projective_plane_minorGcd_dvd hs f hf hd
        (hred p hp hcut) hcut F hF z hprim hz) (by simp)
  rw [sum_empty, add_zero] at h
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end CCDN
