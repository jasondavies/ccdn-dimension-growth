module

public import CCDN.ProjectiveSection
public import CCDN.FilteredHilbertPolynomial

/-! For an actual homogeneous ideal, the filtered Hilbert function is the
successive sum of its graded pieces. This is proved by splitting off the
top homogeneous component in the coordinate quotient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma totalDegree_sub_next_homogeneousComponent_le
    {K σ : Type*} [Field K] (f : MvPolynomial σ K) (N : ℕ)
    (hf : f.totalDegree ≤ N + 1) :
    (f - homogeneousComponent (N + 1) f).totalDegree ≤ N := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro a ha
  change a.degree ≤ N
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at ha
  split_ifs at ha with he
  · exact False.elim (ha (sub_self _))
  · have hfa : f.coeff a ≠ 0 := by simpa only [sub_zero] using ha
    have hd : a.degree ≤ N + 1 := (le_totalDegree (mem_support_iff.mpr hfa)).trans hf
    omega

theorem filteredCoordinateSpace_succ_eq_sup_homogeneous
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (N : ℕ) :
    filteredCoordinateSpace I (N + 1) =
      filteredCoordinateSpace I N ⊔ homogeneousCoordinateSpace I (N + 1) := by
  apply le_antisymm
  · rintro x ⟨f, hf, rfl⟩
    have hfdeg : f.totalDegree ≤ N + 1 := (mem_restrictTotalDegree _ _ _).mp hf
    apply Submodule.mem_sup.mpr
    refine ⟨(Ideal.Quotient.mk I) (f - homogeneousComponent (N + 1) f), ?_,
      (Ideal.Quotient.mk I) (homogeneousComponent (N + 1) f), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨_, (mem_restrictTotalDegree _ _ _).mpr
        (totalDegree_sub_next_homogeneousComponent_le f N hfdeg), rfl⟩
    · exact Submodule.mem_map.mpr ⟨_, homogeneousComponent_mem _ _, rfl⟩
    · simp only [map_sub, sub_add_cancel]
      rfl
  · apply sup_le
    · apply Submodule.map_mono
      intro f hf
      exact (mem_restrictTotalDegree _ _ _).mpr
        (((mem_restrictTotalDegree _ _ _).mp hf).trans (Nat.le_succ N))
    · apply Submodule.map_mono
      intro f hf
      exact (mem_restrictTotalDegree _ _ _).mpr (IsHomogeneous.totalDegree_le hf)

theorem filteredCoordinateSpace_disjoint_next_homogeneous
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) (N : ℕ) :
    Disjoint (filteredCoordinateSpace I N) (homogeneousCoordinateSpace I (N + 1)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨f, hf, rfl⟩ ⟨g, hg, he⟩
  have hfg : f - g ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr he.symm
  have ht := hI (f - g) hfg (N + 1)
  rw [map_sub, homogeneousComponent_eq_zero (N + 1) f
    (lt_of_le_of_lt ((mem_restrictTotalDegree _ _ _).mp hf) (Nat.lt_succ_self N)),
    homogeneousComponent_eq_self hg, zero_sub] at ht
  change (Ideal.Quotient.mk I) f = 0
  calc
    (Ideal.Quotient.mk I) f = (Ideal.Quotient.mk I) g := he.symm
    _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [neg_neg] using I.neg_mem ht)

theorem filteredCoordinateSpace_finrank_succ
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ f ∈ I, ∀ N, homogeneousComponent N f ∈ I) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I (N + 1)) =
      Module.finrank K (filteredCoordinateSpace I N) + projectiveHilbertFunction I (N + 1) := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (filteredCoordinateSpace I N) (homogeneousCoordinateSpace I (N + 1))
  rw [← filteredCoordinateSpace_succ_eq_sup_homogeneous,
    (filteredCoordinateSpace_disjoint_next_homogeneous I hI N).eq_bot,
    finrank_bot, add_zero] at hh
  exact hh

end
end CCDN
