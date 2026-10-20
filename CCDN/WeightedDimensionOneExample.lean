module

public import CCDN.InfiniteWeightEnumeration
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.Nat.Cast.Order.Field

/-! The arbitrary-profile dimension-one boundary of CCDN Lemma 2.2 is
false if its displayed k^(n-2) term is interpreted as 1/k.
Factorial multiplicities make the harmonic excess exact on long blocks.
This does not affect the genuine hypersurface profile, whose layers are
bounded by the multiplicity itself. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

def harmonicExcessProfile (μ : ℕ) (k : ℕ) : ℕ :=
  if k = 0 then 1 else μ + μ / k

lemma harmonicExcessProfile_pos {μ : ℕ} (hμ : 0 < μ) (k : ℕ) :
    0 < harmonicExcessProfile μ k := by
  unfold harmonicExcessProfile
  split_ifs
  · norm_num
  · exact hμ.trans_le (Nat.le_add_right _ _)

lemma harmonicExcessProfile_bound (μ k : ℕ) (hk : 0 < k) :
    (harmonicExcessProfile μ k : ℝ) ≤ (μ : ℝ) + μ / k := by
  simp only [harmonicExcessProfile, Nat.ne_of_gt hk, ite_false, Nat.cast_add]
  exact add_le_add_right Nat.cast_div_le _

lemma harmonicExcessProfile_factorial_succ (K j : ℕ) (hj : j < K) :
    (harmonicExcessProfile K.factorial (j + 1) : ℝ) =
      (K.factorial : ℝ) + K.factorial / (j + 1) := by
  simp only [harmonicExcessProfile, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false, Nat.cast_add]
  rw [Nat.cast_div_charZero (Nat.dvd_factorial (by omega) (by omega))]
  push_cast
  rfl

lemma harmonicExcessProfile_cumulative (K : ℕ) :
    (weightProfileCumulative (harmonicExcessProfile K.factorial) K : ℝ) =
      1 + (K.factorial : ℝ) * (K + (harmonic K : ℝ)) := by
  rw [weightProfileCumulative, sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_sum]
  have hsum :
      (∑ j ∈ range K, (harmonicExcessProfile K.factorial (j + 1) : ℝ)) =
        (K.factorial : ℝ) * (K + (harmonic K : ℝ)) := by
    simp_rw [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [mul_add, mul_sum]
    calc
      _ = ∑ j ∈ range K, ((K.factorial : ℝ) + K.factorial * ((j + 1 : ℕ) : ℝ)⁻¹) := by
        apply sum_congr rfl
        intro j hj
        rw [harmonicExcessProfile_factorial_succ K j (mem_range.mp hj)]
        push_cast
        rfl
      _ = _ := by simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; ring
  have hg0 : harmonicExcessProfile K.factorial 0 = 1 := by simp [harmonicExcessProfile]
  rw [hg0, Nat.cast_one, hsum]
  ring

lemma harmonicExcessProfile_weight_sum (K : ℕ) :
    (∑ j ∈ range (K + 1), (j : ℝ) * harmonicExcessProfile K.factorial j) =
      (K.factorial : ℝ) * K * (K + 1) / 2 + K.factorial * K := by
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have he : (∑ j ∈ range K, (j + 1 : ℝ)) = (K : ℝ) * (K + 1) / 2 := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  calc
    _ = ∑ j ∈ range K, ((K.factorial : ℝ) * (j + 1) + K.factorial) := by
      apply sum_congr rfl
      intro j hj
      rw [harmonicExcessProfile_factorial_succ K j (mem_range.mp hj)]
      push_cast
      have hn : (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, he]
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring

lemma harmonic_real_le_nat (K : ℕ) : (harmonic K : ℝ) ≤ K := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    _ ≤ ∑ _j ∈ range K, (1 : ℝ) := by
      apply sum_le_sum
      intro j _
      exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ j + 1 by omega))
    _ = _ := by simp

/-- Harmonic block excess defeats every fixed linear error coefficient. -/
lemma harmonic_block_excess (C μ K H s E : ℝ)
    (hμ : 1 ≤ μ) (hK : 1 ≤ K) (hH0 : 0 ≤ H) (hHK : H ≤ K)
    (hH : 3 * max C 0 + 2 ≤ H)
    (hs : s = 1 + μ * (K + H)) (hE : E = μ * K * (K + 1) / 2 + μ * K) :
    E < s ^ 2 / (2 * μ) - C * s := by
  have hμ0 : 0 < μ := by linarith
  have hμK : 1 ≤ μ * K := by nlinarith
  have hs0 : 0 < s := by nlinarith
  have hsupper : s ≤ 3 * μ * K := by nlinarith
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hCs : C * s ≤ max C 0 * s :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs0.le
  have hCsup : max C 0 * s ≤ max C 0 * (3 * μ * K) :=
    mul_le_mul_of_nonneg_left hsupper hC
  have hHgap : μ * K * (3 * max C 0 + 2) ≤ μ * K * H :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hsq : μ * μ * (K + H) ^ 2 ≤ s ^ 2 := by
    have hh : 0 ≤ μ * (K + H) := by positivity
    nlinarith
  have hlower : μ * K * (H - 3 / 2) ≤ s ^ 2 / (2 * μ) - E := by
    apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
    rw [hE]
    nlinarith [sq_nonneg (μ * H)]
  nlinarith

/-- No multiplicity-independent linear error works for the printed
dimension-one arbitrary-profile hypothesis, even with c=1 and
infinite monotone enumerations of positive integer profiles. -/
theorem no_uniform_dimension_one_profile_error (C : ℝ) :
    ∃ (μ : ℕ) (g a : ℕ → ℕ) (s : ℕ),
      0 < μ ∧ 0 < s ∧ g 0 = 1 ∧ (∀ k, 0 < g k) ∧
      (∀ k, 0 < k → (g k : ℝ) ≤ (μ : ℝ) + μ / k) ∧
      Monotone a ∧ (∀ k, {i | a i = k}.Finite) ∧
      (∀ k, {i | a i = k}.ncard = g k) ∧
      (∑ i ∈ range s, (a i : ℝ)) < (s : ℝ) ^ 2 / (2 * μ) - C * s := by
  let K : ℕ := ⌊Real.exp (3 * max C 0 + 3)⌋₊
  let μ := K.factorial
  let g := harmonicExcessProfile μ
  have hμ : 0 < μ := Nat.factorial_pos K
  have hH : 3 * max C 0 + 3 ≤ (harmonic K : ℝ) := by
    have h := log_le_harmonic_floor (Real.exp (3 * max C 0 + 3))
      (Real.exp_pos _).le
    simpa only [Real.log_exp] using h
  have hHK := harmonic_real_le_nat K
  have hK : (1 : ℝ) ≤ K := by
    have hC := le_max_right C 0
    linarith
  have hg : ∀ k, 0 < g k := harmonicExcessProfile_pos hμ
  obtain ⟨a, hmono, hfinite, hcount, ha⟩ := exists_positive_profile_enumeration g hg
  let s := weightProfileCumulative g K
  have hs : (s : ℝ) = 1 + (μ : ℝ) * (K + (harmonic K : ℝ)) :=
    harmonicExcessProfile_cumulative K
  have hspos : 0 < s := by
    have hm : (0 : ℝ) < μ := by exact_mod_cast hμ
    have hh : 0 < (s : ℝ) := by
      have hC := le_max_right C 0
      nlinarith
    exact_mod_cast hh
  have hsum : (∑ i ∈ range s, (a i : ℝ)) =
      (μ : ℝ) * K * (K + 1) / 2 + μ * K := by
    rw [← Nat.cast_sum, enumeration_full_block_sum g a hfinite hcount ha K]
    simp only [Nat.cast_sum, Nat.cast_mul]
    exact harmonicExcessProfile_weight_sum K
  refine ⟨μ, g, a, s, hμ, hspos, rfl, hg,
    harmonicExcessProfile_bound μ, hmono, hfinite, hcount, ?_⟩
  apply harmonic_block_excess C μ K (harmonic K) s _ ?_ hK ?_ hHK ?_ hs hsum
  · exact_mod_cast hμ
  · have hC := le_max_right C 0
    linarith
  · linarith

end
end CCDN
