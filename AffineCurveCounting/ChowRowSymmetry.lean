module

public import AffineCurveCounting.ChowIncidenceForm
public import AffineCurveCounting.WeightedHomogeneousTransform

/-! Permuting hyperplanes preserves the actual incidence ideal. Consequently
the separate row degrees of its nonzero principal generator are all equal. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def chowRowPermutation {r s : ℕ} (e : Equiv.Perm (Fin r)) :
    Fin r × Fin s ≃ Fin r × Fin s := Equiv.prodCongr e (Equiv.refl _)

lemma chowIncidenceMap_rename_rows
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

theorem chowIncidenceIdeal_rename_rows_iff
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (e : Equiv.Perm (Fin r))
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    rename (chowRowPermutation e) f ∈ chowIncidenceIdeal r I ↔
      f ∈ chowIncidenceIdeal r I := by
  change chowIncidenceMap r I (rename (chowRowPermutation e) f) = 0 ↔
    chowIncidenceMap r I f = 0
  rw [chowIncidenceMap_rename_rows,
    rename_eq_zero_iff_of_injective (chowIncidenceMap r I f) (chowRowPermutation e).injective]

theorem chow_generator_rename_rows_scalar
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

lemma chow_row_homogeneous_rename
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

theorem exists_chow_incidence_uniform_row_degree
    {K : Type*} [Field K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K) (d : ℕ),
      Irreducible F ∧ chowIncidenceIdeal (m + 1) I = Ideal.span {F} ∧
      ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d := by
  obtain ⟨F,δ,hF,hgen,hδ⟩ := exists_multihomogeneous_chow_incidence_generator I hm
  refine ⟨F,δ 0,hF,hgen,?_⟩
  intro i
  rw [← chow_generator_row_degrees_equal I F hF.ne_zero hgen δ hδ i 0]
  exact hδ i

end
end AffineCurveCounting
