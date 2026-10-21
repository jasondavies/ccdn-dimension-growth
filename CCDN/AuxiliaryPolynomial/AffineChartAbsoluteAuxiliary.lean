/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.AffineChartPrimeDeterminant
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeComparison
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
import CCDN.Algebra.AffineTranslation
import all ArithmeticHeights.BombieriVaaler

/-!
Coefficient-sensitive auxiliary equations with affine-chart good primes.
The positioning transformation fixes the homogenizing coordinate, so the
literal affine good-prime condition survives the coordinate change.

The normalized no-auxiliary comparison for a finite prime set outside which
every large prime is an affine-chart good prime.

Global determinant estimates using geometrically irreducible affine
reductions. Degree-dropping reductions are included whenever the points stay
in the selected unit chart.
-/

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

namespace CCDN
noncomputable section
open MvPolynomial

/-- The comparison retaining the charge of a finite prime set `bad` outside which
every prime above `27 d ^ 4` is an affine-chart good prime. -/
theorem affine_chart_auxiliaryRankComparison {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → stepanovThreshold (d : ℝ) < p →
      AffineChartGoodPrime f z p) :
    AuxiliaryRankComparison order f d z bad :=
  auxiliaryRankComparison_of_determinant_lower order f hf hf0 hd z hz bad
    fun _ _ _ a _ hs hF hi => affine_chart_determinant_log_lower_at_rank (z := z ∘ a) hs f hf hd
      ⟨hF, fun i => hprim (a i), fun i => hz (a i), hi⟩ bad fun p _ hp hcut =>
        have h := hgood p (Finset.mem_sdiff.mp hp).2 hcut
        ⟨h.1, fun i => h.2 (a i)⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Affine-chart good primes are preserved by homogeneous translations, which fix the
homogenizing coordinate. -/
lemma affineChartGoodPrime_homogeneousTranslation {n t : ℕ} (a : Fin (n + 2) → ℤ)
    {f : MvPolynomial (Fin (n + 3)) ℤ} {z : Fin t → IntPoint (n + 3)} (p : ℕ) [Fact p.Prime]
    (h : AffineChartGoodPrime f z p) :
    AffineChartGoodPrime (homogeneousTranslation ℤ a f)
      (fun i => homogeneousPointTranslation (-a) (z i)) p :=
  ⟨by simpa only [affineChart_homogeneousTranslation, affineTranslation_map,
      affineTranslation_irreducible_iff] using h.1,
    fun i => by simpa only [homogeneousPointTranslation, Fin.cons_zero] using h.2 i⟩

/-- The affine-chart version of the absolutely irreducible auxiliary theorem.
The constant depends only on the dimension. The excluded-prime set must satisfy the
displayed good-reduction and unit-chart conditions. -/
theorem affine_chart_absolute_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → stepanovThreshold (d : ℝ) < p →
      AffineChartGoodPrime f z p) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g, IsPointAuxiliary f g M z := by
  have hf0 := ne_zero_of_irreducible_map hir
  have hprim := hzB.primitive
  have hz := hzB.eval_eq_zero
  exact absolute_auxiliary_degree_of_comparison f hf hd hir hzB bad
    (fun a => affine_chart_auxiliaryRankComparison MonomialOrder.lex _
      (homogeneousTranslation_homogeneous a hf)
      ((homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)) hd _
      (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
      (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad
      fun p _ hp hcut => affineChartGoodPrime_homogeneousTranslation a p (hgood p hp hcut))

end
end CCDN
