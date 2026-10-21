module

public import CCDN.Analysis.WeightedSequenceEstimate
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Fintype.Fin

/-! Exact initial weight sums for arbitrary finite or infinite layer profiles.
Initial segments are characterized by their cumulative multiplicities, and
their weight sum is minimal among every selection of distinct generators.
The cutoff is independent of the list length, so no large weights are lost. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

def weightProfileCumulative (r : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ range (k + 1), r j

lemma weightProfileCumulative_mono (r : ℕ → ℕ) : Monotone (weightProfileCumulative r) := by
  intro i j hij
  exact sum_le_sum_of_subset (range_mono (by omega))

/-- A finite list has exactly the multiplicities of the first s weights,
allowing zero layers and profiles of finite total length. -/
def IsInitialWeightSegment (r : ℕ → ℕ) {s : ℕ} (w : Fin s → ℕ) : Prop :=
  ∀ k, (univ.filter fun i => w i ≤ k).card = min s (weightProfileCumulative r k)

/-- The exact layer-cake identity, at any cutoff above every selected weight. -/
lemma sum_weight_tail_counts_eq {s : ℕ} (w : Fin s → ℕ) (K : ℕ)
    (hK : ∀ i, w i ≤ K) :
    (∑ k : Fin K, (univ.filter fun i => k.val < w i).card) = ∑ i, w i := by
  classical
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have hh : (univ.filter fun k : Fin K => k.val < w i).card = w i := by
    rw [Fin.card_filter_val_lt, min_eq_right (hK i)]
  simpa only [card_eq_sum_ones, sum_filter] using hh

/-- Every distinct selection of layer generators costs at least the exact
initial weight sum, including weights exceeding the number of selected rows. -/
theorem initial_weight_sum_le_embedding {s N : ℕ} (r : ℕ → ℕ) (w : Fin s → ℕ)
    (hw : IsInitialWeightSegment r w)
    (t : Fin s ↪ ((j : Fin N) × Fin (r j.val))) :
    ∑ i, w i ≤ ∑ i, (t i).1.val := by
  classical
  let K := univ.sup w
  have htail (k : Fin K) :
      (univ.filter fun i => k.val < w i).card ≤
        (univ.filter fun i => k.val < (t i).1.val).card := by
    have ht := low_weight_card_le r t k.val
    rw [Fin.sum_univ_eq_sum_range] at ht
    change (univ.filter fun i => (t i).1.val ≤ k.val).card ≤
      weightProfileCumulative r k.val at ht
    have hts : (univ.filter fun i => (t i).1.val ≤ k.val).card ≤ s := by
      simpa only [card_univ, Fintype.card_fin] using card_filter_le univ
        (fun i => (t i).1.val ≤ k.val)
    have hwk := hw k.val
    have hwpart := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin s))) (p := fun i => w i ≤ k.val)
    have htpart := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin s))) (p := fun i => (t i).1.val ≤ k.val)
    simp only [card_univ, Fintype.card_fin, not_le] at hwpart htpart
    omega
  rw [← sum_weight_tail_counts_eq w K (fun i => le_sup (mem_univ i))]
  exact (sum_le_sum fun k _ => htail k).trans
    (sum_weight_tail_counts_cutoff_le (fun i => (t i).1.val) K)

/-- Whenever the profile contains at least s generators, its first s weights
exist. They are constructed by the least cumulative cutoff for each index. -/
theorem exists_initial_weight_segment (r : ℕ → ℕ) (s : ℕ)
    (hcapacity : ∃ N, s ≤ weightProfileCumulative r N) :
    ∃ w : Fin s → ℕ, Monotone w ∧ IsInitialWeightSegment r w := by
  classical
  have hex (i : Fin s) : ∃ k, i.val < weightProfileCumulative r k := by
    obtain ⟨N, hN⟩ := hcapacity
    exact ⟨N, i.isLt.trans_le hN⟩
  let w (i : Fin s) := Nat.find (hex i)
  have hw (i : Fin s) (k : ℕ) : w i ≤ k ↔ i.val < weightProfileCumulative r k := by
    constructor
    · intro h
      exact (Nat.find_spec (hex i)).trans_le (weightProfileCumulative_mono r h)
    · exact fun h => Nat.find_le h
  refine ⟨w, ?_, ?_⟩
  · intro i j hij
    apply (hw i (w j)).mpr
    exact (show i.val ≤ j.val from hij).trans_lt (Nat.find_spec (hex j))
  · intro k
    simp only [hw]
    exact Fin.card_filter_val_lt

/-- For a nondecreasing enumeration with the prescribed finite fibers, a
weight lies below k exactly when its index lies below the cumulative count. -/
theorem monotone_weight_le_iff_index_lt_cumulative
    (a r : ℕ → ℕ) (ha : Monotone a)
    (hfinite : ∀ k, {i | a i = k}.Finite)
    (hcount : ∀ k, {i | a i = k}.ncard = r k) (i k : ℕ) :
    a i ≤ k ↔ i < weightProfileCumulative r k := by
  classical
  let T := (range (k + 1)).biUnion (fun j => (hfinite j).toFinset)
  have hmem (j : ℕ) : j ∈ T ↔ a j ≤ k := by
    simp only [T, mem_biUnion, mem_range, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, hj⟩
      omega
    · intro hj
      exact ⟨a j, by omega, rfl⟩
  have hT : T.card = weightProfileCumulative r k := by
    dsimp only [T, weightProfileCumulative]
    rw [card_biUnion]
    · apply sum_congr rfl
      intro j _
      exact (Set.ncard_eq_toFinset_card _ (hfinite j)).symm.trans (hcount j)
    · intro v _ z _ hvz
      apply disjoint_left.mpr
      intro j hjv hjz
      have hv := (hfinite v).mem_toFinset.mp hjv
      have hz := (hfinite z).mem_toFinset.mp hjz
      exact hvz (hv.symm.trans hz)
  constructor
  · intro hi
    have hsub : range (i + 1) ⊆ T := by
      intro j hj
      apply (hmem j).mpr
      exact (ha (by simpa only [mem_range, Nat.lt_succ_iff] using hj)).trans hi
    have hh := card_le_card hsub
    rw [card_range, hT] at hh
    omega
  · intro hi
    by_contra h
    have hsub : T ⊆ range i := by
      intro j hj
      rw [mem_range]
      by_contra hji
      exact h ((ha (by omega)).trans ((hmem j).mp hj))
    have hh := card_le_card hsub
    rw [card_range, hT] at hh
    omega

/-- The first s entries of the paper's nondecreasing sequence satisfy
the exact finite-segment interface. -/
theorem monotone_enumeration_isInitialWeightSegment
    (a r : ℕ → ℕ) (ha : Monotone a)
    (hfinite : ∀ k, {i | a i = k}.Finite)
    (hcount : ∀ k, {i | a i = k}.ncard = r k) (s : ℕ) :
    IsInitialWeightSegment r (fun i : Fin s => a i.val) := by
  intro k
  simp only [monotone_weight_le_iff_index_lt_cumulative a r ha hfinite hcount]
  exact Fin.card_filter_val_lt

end
end CCDN
