/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfacePositioning
/-! Smooth points and full-degree monic positioning in characteristic zero,
for the construction of integral bad-prime witnesses. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_pderiv_ne_zero_of_charZero {K σ : Type*} [Field K] [CharZero K] [Fintype σ] (f : MvPolynomial σ K)
    (hpos : 0 < f.totalDegree) :
    ∃ i, pderiv i f ≠ 0 := by
  classical
  have hne : f.support.Nonempty := by
    by_contra h
    have hz : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [totalDegree, hz] at hpos
  obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup f.support hne
    (fun m => m.sum (fun _ e => e))
  have hsm : m.sum (fun _ e => e) = ∑ i, m i := by
    rw [Finsupp.sum_fintype]
    intro i
    rfl
  have hsum : 0 < ∑ i, m i := by
    have : 0 < m.sum (fun _ e => e) := by simpa only [totalDegree, hdeg] using hpos
    simpa only [hsm] using this
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  let u := m - Finsupp.single i 1
  have hui : u i + 1 = m i := by simp only [u, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
  have hu : u + Finsupp.single i 1 = m := by
    apply tsub_add_cancel_of_le
    intro j
    by_cases hji : j = i
    · subst j; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_eq_of_ne hji]
  have hcast : (m i : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi)
  refine ⟨i, fun hz => ?_⟩
  have hc := congrArg (fun g : MvPolynomial σ K => g.coeff u) hz
  rw [coeff_pderiv, hu] at hc
  change f.coeff m * ((u i : K) + 1) = 0 at hc
  have he : (u i : K) + 1 = (m i : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) hui
  rw [he] at hc
  exact (mul_ne_zero (mem_support_iff.mp hm) hcast) hc

theorem exists_smooth_hypersurface_point_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : Irreducible f) (hpos : 0 < f.totalDegree) :
    ∃ (z : σ → K) (j : σ), eval z f = 0 ∧ eval z (pderiv j f) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_charZero f hpos
  obtain ⟨z, hz, hderiv⟩ := exists_hypersurface_point_partial_ne_zero f hf hpos j hj
  exact ⟨z, j, hz, hderiv⟩

theorem exists_monic_smooth_hypersurface_coordinates_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      Irreducible (normalizedHypersurfaceCoordinates a b hb f) ∧
      (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic ∧
      (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).natDegree = f.totalDegree ∧
      (normalizedHypersurfaceCoordinates a b hb f).totalDegree ≤ f.totalDegree ∧
      eval (0 : Option σ → K) (normalizedHypersurfaceCoordinates a b hb f) = 0 ∧
      eval (0 : Option σ → K) (pderiv none (normalizedHypersurfaceCoordinates a b hb f)) ≠ 0 := by
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_charZero f hf hpos
  obtain ⟨b, hb, hdir, ht⟩ := exists_good_hypersurface_direction_with_coordinate f hf.ne_zero a j hj none
  exact ⟨a, b, hb, hdir, normalizedHypersurfaceCoordinates_irreducible a b hb f hf hdir,
    normalizedHypersurfaceCoordinates_monic a b hb f hdir,
    normalizedHypersurfaceCoordinates_natDegree a b hb f hdir,
    normalizedHypersurfaceCoordinates_totalDegree_le a b hb f,
    normalizedHypersurfaceCoordinates_eval_zero a b hb f ha,
    normalizedHypersurfaceCoordinates_partial_ne_zero a b hb f hdir ht⟩

end
end CCDN
