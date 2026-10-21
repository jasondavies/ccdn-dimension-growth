/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.PositionedAuxiliary
public import CCDN.Auxiliary.IntegerCoefficientHeight
public import CCDN.Algebra.ProjectiveTranslation
import CCDN.Auxiliary.HypersurfaceAuxiliaryScaling
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates
import CCDN.Height.HypersurfacePositionHeight
import CCDN.Plane.HypersurfaceShearInvariance
/-! The coefficient-sensitive auxiliary theorem for arbitrary absolutely
irreducible homogeneous equations in arbitrary coordinates.

The equation is moved into position by a homogeneous translation fixing the
homogenizing coordinate; zeros, primitivity, absolute irreducibility and
nondivisibility are transported along it, and the box grows from `B` to
`(d + 1) B`. `absolute_auxiliary_degree_of_comparison` does this for any finite
prime set whose normalized comparison holds for every translate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def hypersurfaceAuxiliaryPositionConstant (n : ℕ) : ℝ := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)

def hypersurfaceAbsoluteAuxiliaryConstant (n : ℕ) : ℝ :=
  hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n) *
    (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ))

lemma hypersurfaceAbsoluteAuxiliaryConstant_pos (n : ℕ) :
    0 < hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant hypersurfacePositionedAuxiliaryConstant
  positivity

/-- The auxiliary degree bound of CCDN Theorem 3.1.1 with bad-prime factor `b` and
coefficient height `H`. -/
def hypersurfaceAuxiliaryDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B b H

section Translation

variable {n : ℕ}

lemma irreducible_map_homogeneousTranslation {K : Type*} [Field K] (a : Fin (n + 2) → ℤ)
    {f : MvPolynomial (Fin (n + 3)) ℤ} (hir : Irreducible (map (Int.castRingHom K) f)) :
    Irreducible (map (Int.castRingHom K) (homogeneousTranslation ℤ a f)) := by
  rw [homogeneousTranslation_map]
  exact (MulEquiv.irreducible_iff
    (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir

lemma eval_homogeneousTranslation_neg (a : Fin (n + 2) → ℤ)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (z : IntPoint (n + 3)) :
    eval (homogeneousPointTranslation (-a) z) (homogeneousTranslation ℤ a f) = eval z f := by
  rw [homogeneousTranslation_eval]
  change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) z)) f = _
  have he := homogeneousPointTranslation_inverse (-a) z
  simp only [neg_neg] at he
  rw [he]

/-- A form `g` not divisible by the translate of `f` translates back to a
nonmultiple of `f`. -/
lemma not_dvd_homogeneousTranslation_neg (a : Fin (n + 2) → ℤ)
    {f g : MvPolynomial (Fin (n + 3)) ℤ} (hgnd : ¬homogeneousTranslation ℤ a f ∣ g) :
    ¬f ∣ homogeneousTranslation ℤ (-a) g := by
  intro hdvd
  apply hgnd
  have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
  change homogeneousTranslation ℤ a f ∣
    homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) at hh
  rwa [show homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) = g from
    (homogeneousTranslation ℤ a).apply_symm_apply g] at hh

end Translation

/-- Enlarging the box from `B` to `(d + 1) B` and lowering the coefficient height from
`H` to `h ≤ H` cost a factor depending only on the dimension. -/
lemma auxDegreeBound_translate_le {n d : ℕ} (hd : 0 < d) {B b H h : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hh0 : 0 < h) (hhH : h ≤ H) :
    auxDegreeBound n d (((d : ℝ) + 1) * B) b H ≤
      (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let R := ((d : ℝ) + 1) * B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let α := boxExponent n d
  let q := heightExponent n d
  let Q := D * b * B ^ α / h ^ q
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hfactor : ((d : ℝ) + 1) ^ α ≤ E := by
    simpa only [α, E, Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_rpow_factor (r := n + 1) (by omega) hd
  have hRpow : R ^ α ≤ E * B ^ α := by
    rw [show R = ((d : ℝ) + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
    exact mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by linarith) _)
  have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := by
    calc
      _ ≤ D * b * R ^ α / h ^ q := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (Real.rpow_le_rpow hh0.le hhH (by dsimp [q]; positivity))
      _ ≤ D * b * (E * B ^ α) / h ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow (mul_nonneg hD hb))
          (by positivity)
      _ = _ := by dsimp [Q]; ring
  have hlogcost : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log ((d : ℝ) + 1) ≤
      (n + 2 : ℝ) * d := by
    simpa only [Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_log_cost (r := n + 1) (by omega) hd
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hl' : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
    dsimp only [R, l]
    rw [Real.log_mul (by positivity) (by linarith), mul_add]
    have hh := mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n + 2 : ℝ) by positivity)
    linarith
  change D * b * R ^ α / H ^ q + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
    (E + (n + 3 : ℝ)) * (Q + l + D)
  have h1 := mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ
  have h2 := mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl
  have h3 := mul_nonneg hE hD
  nlinarith

/-- The absolutely irreducible case of CCDN Theorem 3.1.1 for any finite prime set
`bad` whose normalized comparison holds for every homogeneous translate of `f` and the
translated points. The constant depends only on dimension; the coefficient height
belongs to the original equation. -/
theorem absolute_auxiliary_degree_of_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ)
    (hcomp : ∀ a : Fin (n + 2) → ℤ, AuxiliaryRankComparison MonomialOrder.lex
      (homogeneousTranslation ℤ a f) d (fun i => homogeneousPointTranslation (-a) (z i)) bad) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g, IsPointAuxiliary f g M z := by
  obtain ⟨⟨hB, hz, hbox⟩, hprim⟩ := hzB
  have hf0 := ne_zero_of_irreducible_map hir
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
    (r := n + 1) (by omega) hd f hf hf0
  let model := homogeneousTranslation ℤ a f
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      hypersurfaceAuxiliaryPositionConstant n * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    simpa only [hypersurfaceAuxiliaryPositionConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, hnR] using hpos
  obtain ⟨M, hbound, g, hg0, hgh, hgz, hgnd⟩ := positioned_auxiliary_degree_of_comparison
    MonomialOrder.lex model (homogeneousTranslation_homogeneous a hf) hd
    (irreducible_map_homogeneousTranslation a hir) H hH hcg (z := w)
    ⟨⟨one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) d]) hB,
      fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i),
      fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j⟩,
      fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i)⟩ bad (hcomp a)
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨M, ?_, homogeneousTranslation ℤ (-a) g,
    (homogeneousTranslation ℤ (-a)).injective.ne (by simpa using hg0),
    homogeneousTranslation_homogeneous (-a) hgh,
    fun i => by rw [homogeneousTranslation_eval]; exact hgz i,
    not_dvd_homogeneousTranslation_neg a hgnd⟩
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n
      (hypersurfaceAuxiliaryPositionConstant n) := by
    unfold hypersurfacePositionedAuxiliaryConstant; positivity
  have htr := auxDegreeBound_translate_le (n := n) hd hB (Real.exp_pos _).le
    (by exact_mod_cast integerCoefficientHeight_pos f hf0)
    (integerCoefficientHeight_le f (by linarith) hcf) (b := primeSetFactor bad)
  refine hbound.trans ((mul_le_mul_of_nonneg_left htr hC).trans_eq ?_)
  unfold hypersurfaceAuxiliaryDegreeBound hypersurfaceAbsoluteAuxiliaryConstant
  ring

/-- The absolutely irreducible case of CCDN Theorem 3.1.1. The constant depends
only on dimension. The coefficient height and bad-prime factor belong to the
original equation. -/
theorem hypersurface_absolute_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  obtain ⟨M, hM, g, hg⟩ := absolute_auxiliary_degree_of_comparison f hf hd hir
    ⟨⟨hB, hz, hbox⟩, hprim⟩ bad
    (fun a => hypersurface_auxiliaryRankComparison MonomialOrder.lex _
      (homogeneousTranslation_homogeneous a hf)
      ((homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)) hd _
      (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
      (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad
      fun p => by rw [hbad, hypersurfaceBadReduction_homogeneousTranslation f hf hf0])
  exact ⟨bad, M, hbad, hM, g, isPointAuxiliary_iff.mp hg⟩

end
end CCDN
