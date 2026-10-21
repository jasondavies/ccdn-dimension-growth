module

public import CCDN.Determinant.HypersurfaceMultiplicityEstimate
public import Mathlib.Data.Set.Card

/-! The weighted-sequence estimate of CCDN Lemma 2.2 in dimensions at least
two. The multiplicity profile is arbitrary; it need not be a hypersurface
Hilbert function. The error is explicit and independent of the multiplicity.

We formulate the result for every finite list whose number of occurrences of
each weight is bounded by the given profile. In particular it applies to
the first `s` terms of the nondecreasing sequence in the paper. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- Tail counting with an arbitrary cutoff, rather than just the list length. -/
lemma sum_weight_tail_counts_cutoff_le {s : ℕ} (w : Fin s → ℕ) (K : ℕ) :
    (∑ k : Fin K, (univ.filter fun i => k.val < w i).card) ≤ ∑ i, w i := by
  classical
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i _
  have hcard : (univ.filter fun k : Fin K => k.val < w i).card ≤ w i := by
    let φ : {k : Fin K // k.val < w i} → Fin (w i) := fun k =>
      ⟨k.val.val, k.property⟩
    have hφ : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      exact Fin.ext (congrArg (fun v : Fin (w i) => v.val) h)
    simpa only [Fintype.card_subtype, Fintype.card_fin] using
      Fintype.card_le_of_injective φ hφ
  simpa only [card_eq_sum_ones, sum_filter] using hcard

/-- The elementary cutoff inequality for any finite list of weights. -/
lemma weights_sum_cutoff {s : ℕ} (w : Fin s → ℕ) (K : ℕ) :
    s * K ≤ (∑ i, w i) +
      ∑ k : Fin K, (univ.filter fun i => w i ≤ k.val).card := by
  classical
  have hpart (k : Fin K) :
      (univ.filter fun i => k.val < w i).card +
        (univ.filter fun i => w i ≤ k.val).card = s := by
    simpa only [not_lt, card_univ, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := univ) (p := fun i => k.val < w i)
  have hsum := congrArg (fun a : Fin K → ℕ => ∑ k, a k) (funext hpart)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    at hsum
  have htail := sum_weight_tail_counts_cutoff_le w K
  rw [Nat.mul_comm K s] at hsum
  omega

lemma weight_count_le_cumulative {s : ℕ} (w : Fin s → ℕ) (g : ℕ → ℕ)
    (hw : ∀ k, (univ.filter fun i => w i = k).card ≤ g k) (k : ℕ) :
    (univ.filter fun i => w i ≤ k).card ≤ ∑ j ∈ range (k + 1), g j := by
  classical
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin s))
    (range (k + 1)) w
  simp only [mem_range, Nat.lt_succ_iff] at h
  rw [← h]
  exact sum_le_sum fun j _ => hw j

/-- A shifted hockey-stick sum. Dropping its nonnegative initial segment
is convenient for arbitrary multiplicity profiles. -/
lemma sum_shifted_choose_le (m t K : ℕ) :
    (∑ j ∈ range K, (m + j + t).choose m) ≤ (m + K + t).choose (m + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have he : m + (K + 1) + t = (m + K + t) + 1 := by omega
    rw [he, Nat.choose_succ_succ']
    omega

/-- The polynomial bound in Lemma 2.2 is dominated by a shifted binomial
profile, retaining its exact leading coefficient. -/
lemma weighted_profile_le_shifted_choose (n c μ : ℕ) (g : ℕ → ℕ)
    (hμ : 0 < μ) (hg0 : g 0 = 1)
    (hg : ∀ k, 0 < k →
      (g k : ℝ) ≤ (μ : ℝ) * (k : ℝ) ^ (n + 1) / (n + 1).factorial +
        c * μ * (k : ℝ) ^ n) (k : ℕ) :
    g k ≤ μ * (n + 1 + k + c * (n + 1).factorial).choose (n + 1) := by
  let t := c * (n + 1).factorial
  by_cases hk : k = 0
  · subst k
    rw [hg0]
    have hc : 1 ≤ (n + 1 + 0 + t).choose (n + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    exact (Nat.succ_le_iff.mpr hμ).trans (Nat.le_mul_of_pos_right _ hc)
  have hfac : (0 : ℝ) < (n + 1).factorial := by positivity
  have hpow : (k : ℝ) ^ (n + 1) + (t : ℝ) * (k : ℝ) ^ n ≤
      ((k + t + 1 : ℕ) : ℝ) ^ (n + 1) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k)
      (show (k : ℝ) ≤ ((k + t + 1 : ℕ) : ℝ) by norm_cast; omega) n
    have hm := mul_le_mul hp
      (show (k : ℝ) + t ≤ ((k + t + 1 : ℕ) : ℝ) by norm_cast; omega)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) + t) (by positivity)
    simpa only [pow_succ, mul_add, mul_comm, mul_left_comm, mul_assoc] using hm
  have hc := Nat.pow_le_choose (α := ℝ) (n + 1) (n + 1 + k + t)
  rw [show n + 1 + k + t + 1 - (n + 1) = k + t + 1 by omega] at hc
  have hm := mul_le_mul_of_nonneg_left
    ((div_le_div_of_nonneg_right hpow hfac.le).trans hc) (Nat.cast_nonneg μ)
  have ht : (t : ℝ) = (c : ℝ) * (n + 1).factorial := by
    simp only [t, Nat.cast_mul]
  rw [ht] at hm
  have he : (μ : ℝ) *
      ((k : ℝ) ^ (n + 1) + c * (n + 1).factorial * (k : ℝ) ^ n) /
        (n + 1).factorial =
      (μ : ℝ) * (k : ℝ) ^ (n + 1) / (n + 1).factorial +
        c * μ * (k : ℝ) ^ n := by
    field_simp
  rw [← mul_div_assoc, he] at hm
  exact_mod_cast (hg k (Nat.pos_of_ne_zero hk)).trans hm

/-- A binomial cumulative capacity gives the sharp weighted sum, independently
of any ordering or Hilbert-function interpretation of the weights. -/
theorem weights_sum_sharp_of_cumulative {s : ℕ} (w : Fin s → ℕ)
    (m μ : ℕ) (hm : 0 < m) (hμ : 0 < μ)
    (hcap : ∀ k, (univ.filter fun i => w i ≤ k).card ≤ μ * (m + k).choose m) :
    ((m.factorial : ℝ) / μ) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤ ∑ i, (w i : ℝ) := by
  have hcut (K : ℕ) :
      s * K ≤ (∑ i, w i) + μ * (m + K).choose (m + 1) := by
    have hc := sum_le_sum (s := (univ : Finset (Fin K))) fun k _ => hcap k.val
    rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun k => (m + k).choose m),
      sum_cumulative_binomial] at hc
    exact (weights_sum_cutoff w K).trans (Nat.add_le_add_left hc _)
  simpa only [Nat.cast_sum] using local_exponent_sharp m s (∑ i, w i) hm hμ hcut

/-- CCDN Lemma 2.2 for every dimension `n+2`, with the explicit constant
`n + 3 + c*(n+1)!`. The profile and the selected weights are arbitrary.
The selected list need not be monotone. -/
theorem weighted_sequence_sum_lower_bound (n c μ s : ℕ) (g : ℕ → ℕ)
    (hμ : 0 < μ) (hg0 : g 0 = 1)
    (hg : ∀ k, 0 < k →
      (g k : ℝ) ≤ (μ : ℝ) * (k : ℝ) ^ (n + 1) / (n + 1).factorial +
        c * μ * (k : ℝ) ^ n)
    (w : Fin s → ℕ) (hw : ∀ k, (univ.filter fun i => w i = k).card ≤ g k) :
    (((n + 2).factorial : ℝ) / μ) ^ (1 / (n + 2 : ℝ)) *
        (n + 2 : ℝ) / (n + 3 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 2 : ℝ)) -
      ((n + 3 : ℝ) + c * (n + 1).factorial) * s ≤ ∑ i, (w i : ℝ) := by
  classical
  let t := c * (n + 1).factorial
  have hcum (k : ℕ) :
      (univ.filter fun i => w i ≤ k).card ≤ μ * (n + 2 + k + t).choose (n + 2) := by
    calc
      _ ≤ ∑ j ∈ range (k + 1), g j := weight_count_le_cumulative w g hw k
      _ ≤ ∑ j ∈ range (k + 1), μ * (n + 1 + j + t).choose (n + 1) :=
        sum_le_sum fun j _ => weighted_profile_le_shifted_choose n c μ g hμ hg0 hg j
      _ = μ * ∑ j ∈ range (k + 1), (n + 1 + j + t).choose (n + 1) := by
        rw [mul_sum]
      _ ≤ μ * (n + 1 + (k + 1) + t).choose (n + 1 + 1) :=
        Nat.mul_le_mul_left μ (sum_shifted_choose_le (n + 1) t (k + 1))
      _ = _ := by
        congr 2
        omega
  have hcap (k : ℕ) :
      (univ.filter fun i => w i + t ≤ k).card ≤ μ * (n + 2 + k).choose (n + 2) := by
    by_cases ht : t ≤ k
    · have he : (univ.filter fun i => w i + t ≤ k) =
          (univ.filter fun i => w i ≤ k - t) := by
        ext i
        simp only [mem_filter, mem_univ, true_and]
        omega
      rw [he]
      have hh := hcum (k - t)
      simpa only [Nat.add_assoc, Nat.sub_add_cancel ht] using hh
    · have he : (univ.filter fun i => w i + t ≤ k) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro i _
        omega
      rw [he, card_empty]
      exact Nat.zero_le _
  have h := weights_sum_sharp_of_cumulative (fun i => w i + t) (n + 2) μ
    (by omega) hμ hcap
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul, sum_add_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, t] at h
  convert (sub_le_iff_le_add.mpr h) using 1
  ring

/-- The first `s` terms of an infinite sequence cannot use more occurrences
of a weight than the whole sequence. -/
lemma initial_weight_count_le {s : ℕ} (w : ℕ → ℕ) (g : ℕ → ℕ)
    (hg : ∀ k, 0 < g k) (hcount : ∀ k, {i | w i = k}.ncard = g k) (k : ℕ) :
    (univ.filter fun i : Fin s => w i.val = k).card ≤ g k := by
  classical
  have hf : {i | w i = k}.Finite :=
    Set.finite_of_ncard_pos (by rw [hcount]; exact hg k)
  let : Fintype ({i : ℕ | w i = k} : Set ℕ) := hf.fintype
  let φ : {i : Fin s // w i.val = k} → ({i : ℕ | w i = k} : Set ℕ) :=
    fun i => ⟨i.val.val, i.property⟩
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective φ hφ
  have hcard : Fintype.card ({i : ℕ | w i = k} : Set ℕ) = g k :=
    (Set.fintypeCard_eq_ncard (s := {i | w i = k})).trans (hcount k)
  rw [hcard] at hc
  simpa only [Fintype.card_subtype] using hc

/-- The paper's initial-segment formulation for arbitrary positive integer
profiles, in every dimension at least two. The nondecreasing assumption is
unnecessary: every enumeration with these multiplicities satisfies the bound. -/
theorem weighted_sequence_initial_sum_lower_bound (n c μ s : ℕ) (g w : ℕ → ℕ)
    (hμ : 0 < μ) (hgpos : ∀ k, 0 < g k) (hg0 : g 0 = 1)
    (hg : ∀ k, 0 < k →
      (g k : ℝ) ≤ (μ : ℝ) * (k : ℝ) ^ (n + 1) / (n + 1).factorial +
        c * μ * (k : ℝ) ^ n)
    (hcount : ∀ k, {i | w i = k}.ncard = g k) :
    (((n + 2).factorial : ℝ) / μ) ^ (1 / (n + 2 : ℝ)) *
        (n + 2 : ℝ) / (n + 3 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 2 : ℝ)) -
      ((n + 3 : ℝ) + c * (n + 1).factorial) * s ≤ ∑ i ∈ range s, (w i : ℝ) := by
  have h := weighted_sequence_sum_lower_bound n c μ s g hμ hg0 hg
    (fun i => w i.val) (initial_weight_count_le w g hgpos hcount)
  rwa [Fin.sum_univ_eq_sum_range (fun i => (w i : ℝ))] at h

/-- The dimension-one version under the hypersurface layer bound.
Unlike a bound involving `μ + c*μ/k`, this hypothesis gives a linear error
uniform in `μ`. -/
theorem weighted_sequence_dimension_one {s μ : ℕ} (hμ : 0 < μ)
    (w : Fin s → ℕ) (hw : ∀ k, (univ.filter fun i => w i = k).card ≤ μ) :
    (s : ℝ) ^ 2 / (2 * μ) - 2 * s ≤ ∑ i, (w i : ℝ) := by
  have hcap (k : ℕ) :
      (univ.filter fun i => w i ≤ k).card ≤ μ * (1 + k).choose 1 := by
    have h := weight_count_le_cumulative w (fun _ => μ) hw k
    simpa only [sum_const, card_range, smul_eq_mul, Nat.choose_one_right,
      Nat.add_comm 1 k, Nat.mul_comm] using h
  have h := weights_sum_sharp_of_cumulative w 1 μ (by norm_num) hμ hcap
  norm_num at h
  convert (sub_le_iff_le_add.mpr h) using 1
  ring

end
end CCDN
