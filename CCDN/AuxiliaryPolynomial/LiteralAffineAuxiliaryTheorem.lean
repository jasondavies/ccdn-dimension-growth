/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
public import CCDN.AuxiliaryPolynomial.LiteralAffineBadPrimes
import CCDN.AuxiliaryPolynomial.AffineAuxiliaryTranslationBound
import CCDN.AuxiliaryPolynomial.AffineBadPrimeTranslation
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.AffineLeadingTranslation
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.AuxiliaryPolynomial.LiteralAffineMinimum
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Height.ScaledHypersurfaceHeight

/-! CCDN Proposition 4.2.1 with the literal affine bad-prime factor.
All box radii, zero constant coefficients and nonabsolute irreducible
equations are included. The chart determinant proof handles good reductions
which lose affine degree.
Here "literal" means the paper's Definition 3.2.1 applied verbatim to the affine
polynomial (`literalAffineBadPrimeFactor`, see `LiteralAffineBadPrimes`), as opposed to
`hypersurfaceBadPrimeFactor`, which also counts primes at which the degree drops. The printed
route through the homogenization does not give this factor
(`Counterexample/HomogenizedBadPrimeFactor.lean`). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every primitive irreducible equation with nonzero constant coefficient
has the affine auxiliary, uniformly over all box radii. -/
private theorem literal_affine_auxiliary_minimum_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f)
    (habs : AbsolutelyIrreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (affineAuxiliaryComparisonConstant n) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (literalAffineBadPrimeFactor f) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := literalAffineBadPrimeFactor f
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := literalAffineBadPrimeFactor_nonneg _
  have hb' : b ≤ literalAffineBadPrimeFactor f := le_rfl
  have hA : 1 ≤ affineAuxiliaryComparisonConstant n := affineAuxiliaryComparisonConstant_one_le n
  by_cases hsmall : B ≤ affineAuxiliaryBoxScale * ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n
  · obtain ⟨g, hg, hgdeg⟩ := literal_unscaled_affine_auxiliary_minimum f hprim hir habs hd
      affineAuxiliaryBoxScale_one_le hB hsmall
    refine ⟨g, hg, hgdeg.trans ?_⟩
    exact (affineMinimumAuxiliaryBound_mono_A n d (le_max_right _ _) hB hL hb).trans
      (affineMinimumAuxiliaryBound_mono_b n d (zero_le_one.trans hA) hB hL hb')
  · have hBA : scalingPrimeRatio ≤ B := by
      have hS : scalingPrimeRatio ≤ affineAuxiliaryBoxScale := by
        have h := scalingPrimeRatio_one_le
        unfold affineAuxiliaryBoxScale
        nlinarith
      have hpow : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n :=
        one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      have hS0 := zero_le_one.trans affineAuxiliaryBoxScale_one_le
      exact (hS.trans (le_mul_of_one_le_right hS0 hpow)).trans (le_of_not_ge hsmall)
    by_cases hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hBA hc hheight
      obtain ⟨g, hg, hgdeg⟩ := literal_prime_scaled_affine_auxiliary_minimum
        f hprim hir habs hd hp hnd scalingPrimeRatio_one_le hB hhi hlo.le
      refine ⟨g, hg, hgdeg.trans ?_⟩
      exact (affineMinimumAuxiliaryBound_mono_A n d (le_max_left _ _) hB hL hb).trans
        (affineMinimumAuxiliaryBound_mono_b n d (zero_le_one.trans hA) hB hL hb')
    · rcases affine_coefficient_height_dichotomy f hir.ne_zero hprim hB with hh | hg
      · have hcoef : Real.log |(f.coeff 0 : ℝ)| ≤ Real.log (integerCoefficientHeight f : ℝ) :=
          Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc))
            (coefficient_abs_le_integerCoefficientHeight f 0)
        have hcut := affine_coefficient_height_cutoff (n + 2) d scalingPrimeRatio_one_le hB
          ((le_of_not_gt hheight).trans (hcoef.trans hh))
        exact (hsmall hcut).elim
      · obtain ⟨g, hg, hgdeg⟩ := hg
        refine ⟨g, hg, ?_⟩
        have hgR : (g.totalDegree : ℝ) ≤ d := by exact_mod_cast hgdeg
        exact hgR.trans (degree_le_affineMinimumAuxiliaryBound n hd (zero_le_one.trans hA) hB hL
          (literalAffineBadPrimeFactor_nonneg f))


private theorem literal_affine_hypersurface_auxiliary_absolute {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f)
    (habs : AbsolutelyIrreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (literalAffineBadPrimeFactor f) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := literalAffineBadPrimeFactor f
  let A := affineAuxiliaryComparisonConstant n
  have hA : 0 ≤ A := zero_le_one.trans (affineAuxiliaryComparisonConstant_one_le n)
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := literalAffineBadPrimeFactor_nonneg f
  obtain ⟨a, ha, hc⟩ := exists_bounded_affine_translation_nonzero_constant f hir.ne_zero
  let t := affineTranslation ℤ a f
  have htprim : PrimitiveIntegerPolynomial t := hprim.translate_affine a
  have htir : Irreducible t := (affineTranslation_irreducible_iff a f).mpr hir
  have htd : t.totalDegree = d := affineTranslation_totalDegree a f
  have htdpos : 0 < t.totalDegree := htd ▸ hd
  have hB' : 1 ≤ B + d := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have htabs : AbsolutelyIrreducible t := by
    simpa only [AbsolutelyIrreducible, t, affineTranslation_map, affineTranslation_irreducible_iff]
      using habs
  obtain ⟨g, hg, hgdeg⟩ :=
    literal_affine_auxiliary_minimum_nonzero_constant t htprim htir htabs htdpos hc hB'
  have habox (j) : |(a j : ℝ)| ≤ d := by
    have h0 : (0 : ℝ) ≤ a j := by exact_mod_cast (ha j).1
    rw [abs_of_nonneg h0]
    exact_mod_cast (ha j).2
  obtain ⟨G, hG, hGdeg⟩ := affine_auxiliary_translation_transport f g a hg habox
  refine ⟨G, hG, ?_⟩
  have htle : (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n d A (B + d) L b := by
    have htop : homogeneousComponent t.totalDegree t = homogeneousComponent d f :=
      affineTranslation_leading_homogeneousComponent a f
    rw [htop, htd] at hgdeg
    simpa only [t, literalAffineBadPrimeFactor_affineTranslation] using hgdeg
  rw [hGdeg]
  apply (htle.trans (affineMinimumAuxiliaryBound_translation hd hA hB hL hb)).trans
  have hh := mul_le_mul_of_nonneg_left
    (affineMinimumAuxiliaryBound_le_expression n d hA hB hL hb)
    (show 0 ≤ 2 * Real.exp ((n : ℝ) + 2) by positivity)
  dsimp only [affineHypersurfaceAuxiliaryConstant, A]
  convert hh using 1
  ring


/-- CCDN Proposition 4.2.1 with the literal affine bad-prime factor: for a primitive irreducible
integer polynomial `f` of positive degree `d` in `n + 2` variables and `B ≥ 1`, there is a
nonzero polynomial `g`, not divisible by `f`, vanishing at all integer zeros of `f` in the box of
radius `B`, whose degree is at most `affineHypersurfaceAuxiliaryConstant n` times
`affineAuxiliaryDegreeExpression`, evaluated at the height of the leading form of `f` and
`literalAffineBadPrimeFactor f`. -/
theorem literal_affine_hypersurface_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (literalAffineBadPrimeFactor f) ∧
      ∀ x : IntPoint (n + 2), InBox x B → eval x f = 0 → eval x g = 0 := by
  by_cases habs : AbsolutelyIrreducible f
  · exact exists_isBoxAuxiliary_and_iff.mp
      (literal_affine_hypersurface_auxiliary_absolute f hprim hir habs hd hB)
  · simpa only [literalAffineBadPrimeFactor_eq_zero f habs,
      hypersurfaceBadPrimeFactor_eq_zero f habs] using
      exists_isBoxAuxiliary_and_iff.mp (affine_hypersurface_auxiliary f hprim hir hd hB)

end
end CCDN
