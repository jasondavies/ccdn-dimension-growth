/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AbsoluteAuxiliary
public import CCDN.Auxiliary.AffineChartPrimeDeterminant
import CCDN.Algebra.AffineTranslation
import CCDN.Auxiliary.AffineChartAuxiliaryComparison
/-! Coefficient-sensitive auxiliary equations with affine-chart good primes.
The positioning transformation fixes the homogenizing coordinate, so the
literal affine good-prime condition survives the coordinate change. -/

@[expose] public section
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
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → stepanovThreshold (d : ℝ) < p →
      AffineChartGoodPrime f z p)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  exact absolute_auxiliary_degree_of_comparison f hf hd hir z hprim hz bad
    (fun a => affine_chart_auxiliaryRankComparison MonomialOrder.lex _
      (homogeneousTranslation_homogeneous a hf)
      ((homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)) hd _
      (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
      (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad
      fun p _ hp hcut => affineChartGoodPrime_homogeneousTranslation a p (hgood p hp hcut))
    hB hbox

end
end CCDN
