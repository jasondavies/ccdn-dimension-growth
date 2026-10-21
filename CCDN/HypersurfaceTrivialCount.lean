module

public import CCDN.Plane
public import CCDN.PrimitiveNormalization
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! The exact elementary box bound for a nonzero affine hypersurface in
any number of variables: the hypersurface case of CCDN Lemma 4.1.1. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem integer_hypersurface_zero_box_card_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    (((integerBox (n + 1) B).filter (fun x => eval x f = 0)).card : ℝ) ≤
      (f.totalDegree : ℝ) * (2 * B + 1) ^ n := by
  classical
  let S := Finset.Icc (-⌊B⌋) ⌊B⌋
  have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hSne : S.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨by omega, hfloor⟩⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have h := schwartz_zippel_totalDegree hf S
  have hR : (((integerBox (n + 1) B).filter (fun x => eval x f = 0)).card : ℝ) /
      (S.card : ℝ) ^ (n + 1) ≤ f.totalDegree / (S.card : ℝ) := by
    simpa only [NNRat.cast_div, NNRat.cast_pow, NNRat.cast_natCast, integerBox, S] using
      (NNRat.cast_le (K := ℝ)).mpr h
  have hcard : (((integerBox (n + 1) B).filter (fun x => eval x f = 0)).card : ℝ) ≤
      f.totalDegree * (S.card : ℝ) ^ n := by
    have hh := (div_le_iff₀ (pow_pos hSpos (n + 1))).mp hR
    convert hh using 1
    rw [pow_succ]
    field_simp
  have hScard : (S.card : ℝ) ≤ 2 * B + 1 := by
    dsimp only [S]
    rw [Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith [Int.floor_le B]
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hSpos.le hScard n) (Nat.cast_nonneg _))

theorem integer_hypersurface_count_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (f.totalDegree : ℝ) * (2 * B + 1) ^ n := by
  classical
  have hset : integralPoints (zeroLocus (map (Int.castRingHom ℚ) f)) B =
      (integerBox (n + 1) B).filter (fun x => eval x f = 0) := by
    apply Finset.filter_congr
    intro x _
    change eval (rationalPoint x) (map (Int.castRingHom ℚ) f) = 0 ↔ eval x f = 0
    have he : ((eval x f : ℤ) : ℚ) =
        eval (rationalPoint x) (map (Int.castRingHom ℚ) f) :=
      map_eval (Int.castRingHom ℚ) x f
    rw [← he]
    exact Int.cast_eq_zero
  unfold count
  rw [hset]
  exact integer_hypersurface_zero_box_card_le f hf hB

/-- The exact degree-times-box-volume bound, independent of coefficient
height, for every nonzero rational hypersurface equation. -/
theorem rational_hypersurface_count_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) * (2 * B + 1) ^ n := by
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model f hf
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at he
    exact mul_ne_zero (C_eq_zero.not.mpr ha) hf he.symm
  have hdegree : g.totalDegree = f.totalDegree := rational_scalar_model_degree ha hf he
  have hzero : zeroLocus (map (Int.castRingHom ℚ) g) = zeroLocus f := by
    ext x
    exact rational_scalar_model_zero_iff ha he x
  simpa only [hzero, hdegree] using integer_hypersurface_count_le g hg0 hB

end
end CCDN
