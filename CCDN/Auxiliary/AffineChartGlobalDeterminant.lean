/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AffineChartPrimeDeterminant
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
import all ArithmeticHeights.BombieriVaaler

/-! Global determinant estimates using geometrically irreducible affine
reductions. Degree-dropping reductions are included whenever the points stay
in the selected unit chart. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for
maximal minors and common-degree homogeneous evaluation columns. -/
theorem affine_chart_determinant_log_lower_at_rank {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (bad : Finset ℕ)
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      stepanovThreshold (d : ℝ) < p →
      AffineChartGoodPrime f z p) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors hs hd bad
    (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent)) fun p hp hcut => ?_
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hir, hunit⟩ := hred p hp hcut
  exact affine_chart_minorGcd_dvd f hf hir hcut F hev.isHomogeneous z hev.primitive
    hev.eval_eq_zero hunit

end
end CCDN
