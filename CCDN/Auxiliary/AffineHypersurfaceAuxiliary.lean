module

public import CCDN.Auxiliary.AffineAuxiliaryCases
public import CCDN.Auxiliary.AffineBadPrimeTranslation
public import CCDN.Auxiliary.AffineAuxiliaryTranslationBound
/-! The affine auxiliary theorem in every positive dimension and degree,
with the degree-loss-inclusive geometric bad-prime factor. This distinction
from the literal affine wording of CCDN Definition 3.2.1 is intentional. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def affineAuxiliaryDegreeExpression (n d : ℕ) (B L b : ℝ) : ℝ :=
  (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
    (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

def affineHypersurfaceAuxiliaryConstant (n : ℕ) : ℝ :=
  (2 * Real.exp ((n : ℝ) + 2)) * hypersurfaceAbsoluteAuxiliaryConstant n *
    (max (affineHeightTransferConstant n) (Real.exp 1) *
      affineAuxiliaryComparisonConstant n + 1)

lemma affineHypersurfaceAuxiliaryConstant_pos (n : ℕ) :
    0 < affineHypersurfaceAuxiliaryConstant n := by
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hA := zero_le_one.trans (affineAuxiliaryComparisonConstant_one_le n)
  have hC := hypersurfaceAbsoluteAuxiliaryConstant_pos n
  unfold affineHypersurfaceAuxiliaryConstant
  positivity

lemma affineMinimumAuxiliaryBound_le_expression (n d : ℕ) {A B L b : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineMinimumAuxiliaryBound n d A B L b ≤
      (hypersurfaceAbsoluteAuxiliaryConstant n *
        (max (affineHeightTransferConstant n) (Real.exp 1) * A + 1)) *
          affineAuxiliaryDegreeExpression n d B L b := by
  let K := max (affineHeightTransferConstant n) (Real.exp 1) * A
  let M := (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))))
  let E := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hK : 0 ≤ K := mul_nonneg ((Real.exp_pos 1).le.trans (le_max_right _ _)) hA
  have hmin : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hb)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hE : 0 ≤ E := by
    have := Real.log_nonneg hB
    dsimp only [E]
    positivity
  have hh : K * M + E ≤ (K + 1) * (M + E) := by nlinarith [mul_nonneg hK hE]
  have hh' := mul_le_mul_of_nonneg_left hh (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound affineAuxiliaryDegreeExpression
  dsimp only [K, M, E] at hh'
  convert hh' using 1 <;> ring

/-- Every primitive irreducible integer affine hypersurface admits the
coefficient-sensitive auxiliary in the complete minimum form, using the
defined geometric bad-prime factor (which includes degree-dropping primes).
The constant depends only on the dimension. -/
theorem affine_hypersurface_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor f
  let A := affineAuxiliaryComparisonConstant n
  have hA : 0 ≤ A := zero_le_one.trans (affineAuxiliaryComparisonConstant_one_le n)
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg f
  obtain ⟨a, ha, hc⟩ := exists_bounded_affine_translation_nonzero_constant f hir.ne_zero
  let t := affineTranslation ℤ a f
  have htprim : PrimitiveIntegerPolynomial t := hprim.translate_affine a
  have htir : Irreducible t := (affineTranslation_irreducible_iff a f).mpr hir
  have htd : t.totalDegree = d := affineTranslation_totalDegree a f
  have htdpos : 0 < t.totalDegree := htd ▸ hd
  have hB' : 1 ≤ B + d := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ :=
    affine_auxiliary_minimum_nonzero_constant t htprim htir htdpos hc hB'
  have habox (j) : |(a j : ℝ)| ≤ d := by
    have h0 : (0 : ℝ) ≤ a j := by exact_mod_cast (ha j).1
    rw [abs_of_nonneg h0]
    exact_mod_cast (ha j).2
  obtain ⟨G, hG0, hGnd, hGdeg, hGz⟩ :=
    affine_auxiliary_translation_transport f g a hg0 hgnd habox hgz
  refine ⟨G, hG0, hGnd, ?_, hGz⟩
  have htle : (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n d A (B + d) L b := by
    have htop : homogeneousComponent t.totalDegree t = homogeneousComponent d f :=
      affineTranslation_leading_homogeneousComponent a f
    rw [htop, htd] at hgdeg
    simpa only [t, hypersurfaceBadPrimeFactor_affineTranslation] using hgdeg
  rw [hGdeg]
  apply (htle.trans (affineMinimumAuxiliaryBound_translation hd hA hB hL hb)).trans
  have hh := mul_le_mul_of_nonneg_left
    (affineMinimumAuxiliaryBound_le_expression n d hA hB hL hb)
    (show 0 ≤ 2 * Real.exp ((n : ℝ) + 2) by positivity)
  dsimp only [affineHypersurfaceAuxiliaryConstant, A]
  convert hh using 1
  ring

end
end CCDN
