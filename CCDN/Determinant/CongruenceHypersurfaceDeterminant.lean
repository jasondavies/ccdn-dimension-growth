/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
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
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (bad : Finset ℕ)
    (P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)))
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      stepanovThreshold (d : ℝ) < p →
      HasGoodReduction f p) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors_congruence hs hd bad P hPbad hP v
    (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent))
    (fun p hp hcut => ?_) hcong
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hf0, hir⟩ := hred p hp hcut
  simpa only [hypersurfaceDeterminantMain_div] using
    projective_hypersurface_minorGcd_dvd f hf hd hf0 hir hcut F hev.isHomogeneous z hev.primitive
      hev.eval_eq_zero

end
end CCDN
