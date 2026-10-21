/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectivePermutation
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDNPaper.Center.ProjectiveChowIncidence
import CCDNPaper.Center.ProjectiveIncidenceClosed
import CCDNPaper.Hilbert.FilteredHilbertEquiv

/-! Coordinate permutations transport the homogeneous ideal and
projective hyperplane incidence, without choosing projective representatives. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Permuting the coordinates of a homogeneous ideal gives a homogeneous ideal. -/
theorem projectivePermutedIdeal_homogeneous
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (e : Equiv.Perm (Fin (n + 1))) :
    ∀ f ∈ projectivePermutedIdeal J e, ∀ M,
      homogeneousComponent M f ∈ projectivePermutedIdeal J e := by
  intro f hf M
  rw [mem_projectivePermutedIdeal, rename_homogeneousComponent]
  exact hJ _ ((mem_projectivePermutedIdeal J e f).mp hf) M

/-- Permuting the coordinates of an ideal does not change its filtered Hilbert polynomial. -/
theorem projectivePermutedIdeal_filteredHilbertPolynomial
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (e : Equiv.Perm (Fin (n + 1))) :
    filteredHilbertPolynomial (projectivePermutedIdeal J e) =
      filteredHilbertPolynomial J := by
  have heq : projectivePermutedIdeal J e = J.map (renameEquiv K e.symm) := by
    ext f
    rw [mem_projectivePermutedIdeal]
    rw [Ideal.mem_map_of_equiv (renameEquiv K e.symm)]
    constructor
    · intro hf
      exact ⟨rename e f, hf, (renameEquiv K e).symm_apply_apply f⟩
    · rintro ⟨g,hg,he⟩
      rw [← he]
      change (renameEquiv K e) ((renameEquiv K e).symm g) ∈ J
      rwa [AlgEquiv.apply_symm_apply]
  rw [heq]
  exact (filteredHilbertPolynomial_renameEquiv J e.symm).symm

private lemma coordinate_comp_equiv_ne_zero
    {K σ : Type*} [Zero K] (e : Equiv.Perm σ) (x : σ → K) (hx : x ≠ 0) :
    x ∘ e ≠ 0 := by
  intro h
  apply hx
  funext i
  have hh := congrFun h (e.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using hh

/-- The permutation of hyperplane coefficients `Fin r × Fin s` that applies the coordinate
permutation `e` within each hyperplane row. -/
def chowColumnPermutation {r s : ℕ} (e : Equiv.Perm (Fin s)) :
    Fin r × Fin s ≃ Fin r × Fin s := Equiv.prodCongr (Equiv.refl _) e

/-- For a homogeneous ideal `J`, a hyperplane tuple `U` meets the projective variety of `J` if and
only if the tuple `U ∘ chowColumnPermutation e` meets the variety of the coordinate-permuted
ideal. -/
theorem projectiveChowIncidenceLocus_permuted
    {K : Type*} [Field K] {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : IsHomogeneousIdeal J)
    (e : Equiv.Perm (Fin (n + 1))) (U : Fin r × Fin (n + 1) → K) :
    U ∘ chowColumnPermutation e ∈ projectiveChowIncidenceLocus r (projectivePermutedIdeal J e) ↔
      U ∈ projectiveChowIncidenceLocus r J := by
  rw [projectiveChowIncidenceLocus_iff_cone _ (projectivePermutedIdeal_homogeneous J hJ e),
    projectiveChowIncidenceLocus_iff_cone J hJ]
  constructor
  · rintro ⟨y,hy,hyJ,hrel⟩
    refine ⟨y ∘ e.symm, coordinate_comp_equiv_ne_zero e.symm y hy, ?_, ?_⟩
    · intro f hf
      have hmem : rename e.symm f ∈ projectivePermutedIdeal J e := by
        rw [mem_projectivePermutedIdeal]
        change (renameEquiv K e) ((renameEquiv K e).symm f) ∈ J
        rwa [AlgEquiv.apply_symm_apply]
      simpa only [eval_rename] using hyJ _ hmem
    · intro i
      have hs := Equiv.sum_comp e.symm (fun j => U (i,e j) * y j)
      simp only [Equiv.apply_symm_apply] at hs
      exact hs.trans (hrel i)
  · rintro ⟨x,hx,hxJ,hrel⟩
    refine ⟨x ∘ e, coordinate_comp_equiv_ne_zero e x hx, ?_, ?_⟩
    · intro f hf
      have hh := hxJ _ ((mem_projectivePermutedIdeal J e f).mp hf)
      simpa only [eval_rename] using hh
    · intro i
      exact (Equiv.sum_comp e (fun j => U (i,j) * x j)).trans (hrel i)

end
end CCDN
