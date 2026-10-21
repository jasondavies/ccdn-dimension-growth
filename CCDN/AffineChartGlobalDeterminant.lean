module

public import CCDN.AffineChartPrimeDeterminant
public import CCDN.HypersurfaceDeterminantRank
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
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0)) :
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + (∑ p ∈ bad, Real.log p / p)) -
          hypersurfaceDeterminantError n) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  refine hypersurface_log_lower_at_rank_of_local_divisors hs hd bad
    (lt_of_lt_of_le one_pos (Int.Matrix.one_le_minorGcd hrows)) fun p hp hcut => ?_
  have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
  obtain ⟨hir, hunit⟩ := hred p hp hcut
  exact affine_chart_hypersurface_minorGcd_sharp f hf hir hcut F hF z hprim hz hunit

end
end CCDN
