module

public import CCDN.Determinant.HypersurfaceDeterminantRank
import all ArithmeticHeights.BombieriVaaler

/-! Congruence-refined global hypersurface determinant bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for
maximal minors and common-degree homogeneous evaluation columns. -/
theorem hypersurface_determinant_log_lower_at_rank_congruence {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)))
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      HasGoodReduction f p) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors_congruence hs hd bad P hPbad hP v
    (lt_of_lt_of_le one_pos (Int.Matrix.one_le_minorGcd hrows)) (fun p hp hcut => ?_) hcong
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hf0, hir⟩ := hred p hp hcut
  simpa only [hypersurfaceDeterminantMain_div] using
    projective_hypersurface_minorGcd_dvd f hf hd hf0 hir hcut F hF z hprim hz

end
end CCDN
