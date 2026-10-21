/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.ChowIncidenceIdeal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDNPaper.Algebra.WeightedHomogeneousTransform
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Permuting hyperplanes preserves the incidence ideal. Consequently
the separate row degrees of its nonzero principal generator are all equal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def chowRowPermutation {r s : ℕ} (e : Equiv.Perm (Fin r)) :
    Fin r × Fin s ≃ Fin r × Fin s := Equiv.prodCongr e (Equiv.refl _)

private lemma chowIncidenceMap_rename_rows
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (e : Equiv.Perm (Fin r))
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    chowIncidenceMap r I (rename (chowRowPermutation e) f) =
      rename (chowRowPermutation e) (chowIncidenceMap r I f) := by
  have hh : (chowIncidenceMap r I).toRingHom.comp
      (rename (chowRowPermutation e)).toRingHom =
      (rename (chowRowPermutation e)).toRingHom.comp
        (chowIncidenceMap r I).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chowIncidenceMap]
    · rintro ⟨i,j⟩
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [chowIncidenceMap, chowRowPermutation]
  exact RingHom.congr_fun hh f

private theorem chowIncidenceIdeal_rename_rows_iff
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (e : Equiv.Perm (Fin r))
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    rename (chowRowPermutation e) f ∈ chowIncidenceIdeal r I ↔
      f ∈ chowIncidenceIdeal r I := by
  change chowIncidenceMap r I (rename (chowRowPermutation e) f) = 0 ↔
    chowIncidenceMap r I f = 0
  rw [chowIncidenceMap_rename_rows,
    rename_eq_zero_iff_of_injective (chowIncidenceMap r I f) (chowRowPermutation e).injective]

private theorem chow_generator_rename_rows_scalar
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (e : Equiv.Perm (Fin r))
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : F ≠ 0)
    (hgen : chowIncidenceIdeal r I = Ideal.span {F}) :
    ∃ c : K, c ≠ 0 ∧ rename (chowRowPermutation e) F = C c * F := by
  have hm : F ∈ chowIncidenceIdeal r I := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton F)
  have hr := (chowIncidenceIdeal_rename_rows_iff I e F).mpr hm
  rw [hgen, Ideal.mem_span_singleton] at hr
  obtain ⟨g,hg⟩ := hr
  have hrename : rename (chowRowPermutation e) F ≠ 0 :=
    (rename_eq_zero_iff_of_injective F (chowRowPermutation e).injective).not.mpr hF
  have hg0 : g ≠ 0 := by
    intro hz
    exact hrename (by simpa only [hz, mul_zero] using hg)
  have hdeg : g.totalDegree = 0 := by
    have hh := totalDegree_rename_le (chowRowPermutation e) F
    rw [hg, totalDegree_mul_of_isDomain hF hg0] at hh
    omega
  have hgC : g = C (g.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdeg
  refine ⟨g.coeff 0, ?_, ?_⟩
  · intro hz
    exact hg0 (hgC.trans (by rw [hz, map_zero]))
  · calc
      rename (chowRowPermutation e) F = F * g := hg
      _ = F * C (g.coeff 0) := congrArg (fun q => F * q) hgC
      _ = C (g.coeff 0) * F := mul_comm _ _

private lemma chow_row_homogeneous_rename
    {K : Type*} [Field K] {r s : ℕ}
    (e : Equiv.Perm (Fin r)) (i : Fin r)
    (F : MvPolynomial (Fin r × Fin s) K) (d : ℕ)
    (hF : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    (rename (chowRowPermutation e) F).IsWeightedHomogeneous
      (chowRowWeight (e i)) d := by
  apply weighted_homogeneous_rename (chowRowWeight i) (chowRowWeight (e i))
    (chowRowPermutation e) _ F d hF
  intro q
  simp [chowRowWeight, chowRowPermutation]

/-- If a nonzero polynomial `F` generates the Chow incidence ideal of `I` and is weighted
homogeneous of degree `δ i` in each row `i` of hyperplane coefficients, then all the row degrees
`δ i` are equal. -/
theorem chow_generator_row_degrees_equal
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : F ≠ 0)
    (hgen : chowIncidenceIdeal r I = Ideal.span {F})
    (δ : Fin r → ℕ) (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i))
    (i j : Fin r) : δ i = δ j := by
  classical
  let e := Equiv.swap i j
  obtain ⟨c,hc,he⟩ := chow_generator_rename_rows_scalar I e F hF hgen
  have hi := chow_row_homogeneous_rename e i F (δ i) (hδ i)
  have hj := (hδ j).C_mul c
  have hn : C c * F ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hF
  rw [he] at hi
  have hei : e i = j := Equiv.swap_apply_left i j
  rw [hei] at hi
  exact IsWeightedHomogeneous.inj_right hn hi hj

section

/-! Total degree is the sum of the hyperplane block degrees. -/

open MvPolynomial

private lemma sum_chow_row_weight {r s : ℕ} (e : (Fin r × Fin s) →₀ ℕ) :
    ∑ i, Finsupp.weight (chowRowWeight i) e = e.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp [chowRowWeight]

/-- A polynomial in rows of variables indexed by `Fin r × Fin s` that is weighted homogeneous of
degree `δ i` in each row `i` is homogeneous of total degree `∑ i, δ i`. -/
theorem chow_rows_homogeneous_total_degree
    {K : Type*} [CommRing K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (δ : Fin r → ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) :
    F.IsHomogeneous (∑ i, δ i) := by
  intro e he
  have hw : Finsupp.weight (1 : Fin r × Fin s → ℕ) e = e.degree := by
    simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
  rw [hw, ← sum_chow_row_weight e]
  exact Finset.sum_congr rfl (fun i _ => hδ i he)

/-- A nonzero polynomial in `r` rows of variables that is weighted homogeneous of degree `d` in each
row has total degree `r * d`. -/
theorem chow_uniform_row_degree_totalDegree
    {K : Type*} [CommRing K] {r s : ℕ}
    (F : MvPolynomial (Fin r × Fin s) K) (hF : F ≠ 0) (d : ℕ)
    (hδ : ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) :
    F.totalDegree = r * d := by
  have hh := chow_rows_homogeneous_total_degree F (fun _ => d) hδ
  simpa using hh.totalDegree hF

end

end
end CCDN
