module

public import AffineCurveCounting.PrincipalSectionPurity
public import AffineCurveCounting.ProperSectionHilbert
public import AffineCurveCounting.PureVarietyGridBound

/-! The exact degree and grid bound for a proper principal section.
Both purity and the intersection multiplicity budget are derived from the
original prime ideal and section equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma filteredCoordinateSpace_finrank_antitone_ideal
    {K σ : Type*} [Field K] [Fintype σ]
    (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace J N) ≤
      Module.finrank K (filteredCoordinateSpace I N) := by
  let φ : (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J)
      (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hf))
  have hmap : (filteredCoordinateSpace I N).map φ.toLinearMap =
      filteredCoordinateSpace J N := by
    ext x
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact Submodule.mem_map.mpr ⟨Ideal.Quotient.mk I f,
        Submodule.mem_map.mpr ⟨f, hf, rfl⟩, rfl⟩
  have hh := finrank_map_add_kernel_subspace_le φ.toLinearMap
    (filteredCoordinateSpace I N) ⊥ bot_le bot_le
  rw [hmap] at hh
  simpa only [finrank_bot, add_zero] using hh

theorem principal_section_hilbert_dimension
    {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial (Fin n) K) (hf : f ∉ I) (hfdeg : 0 < f.totalDegree)
    (hsection : I ⊔ Ideal.span {f} ≠ ⊤) :
    (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = m := by
  apply le_antisymm (proper_section_hilbert_dimension_leadingCoeff I m hdim f hf hfdeg hsection).1
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hsection
  have hPdim := principal_section_minimalPrime_hilbert_dimension I hdim f hf P hP
  rw [← hPdim]
  exact filteredHilbertPolynomial_natDegree_le P _ hP.isPrime.ne_top
    (filteredCoordinateSpace_finrank_antitone_ideal _ _ hP.le)

theorem principal_section_degree_budget
    {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (f : MvPolynomial (Fin n) K) (hf : f ∉ I) (hfdeg : 0 < f.totalDegree)
    (hsection : I ⊔ Ideal.span {f} ≠ ⊤) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d * f.totalDegree ∧
      (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = m ∧
      (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).leadingCoeff =
        (e : ℚ) / m.factorial := by
  have hdimJ := principal_section_hilbert_dimension I hdim f hf hfdeg hsection
  obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity
    (I ⊔ Ideal.span {f}) hsection
  rw [hdimJ] at hlc
  refine ⟨e, he, ?_, hdimJ, hlc⟩
  have hh := (proper_section_hilbert_dimension_leadingCoeff I m hdim f hf hfdeg hsection).2 hdimJ
  rw [hlc, hdegree, Nat.factorial_succ, Nat.cast_mul] at hh
  have hfac : (0 : ℚ) < m.factorial := by positivity
  have heq : (d : ℚ) / ((m + 1) * m.factorial) * (m + 1) * f.totalDegree =
      ((d * f.totalDegree : ℕ) : ℚ) / m.factorial := by
    push_cast
    field_simp
  rw [show ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 by push_cast; rfl, heq] at hh
  exact_mod_cast (div_le_div_iff_of_pos_right hfac).mp hh

/-- Sharp Bezout-plus-grid count with the actual section and actual
minimal-prime decomposition constructed inside the proof. -/
theorem principal_section_grid_card_le
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (f : MvPolynomial (Fin n) K) (hf : f ∉ I)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ g ∈ I, eval x g = 0)
    (hsectionzero : ∀ x ∈ s, eval x f = 0)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d * f.totalDegree * S.card ^ m := by
  classical
  let J := I ⊔ Ideal.span {f}
  have hzJ (x) (hx : x ∈ s) : ∀ g ∈ J, eval x g = 0 := by
    change J ≤ RingHom.ker (eval x)
    apply sup_le (hzero x hx)
    apply Ideal.span_le.mpr
    intro g hg
    obtain rfl := Set.mem_singleton_iff.mp hg
    exact hsectionzero x hx
  by_cases hJ : J = ⊤
  · have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hzJ x hx 1 (by rw [hJ]; exact Submodule.mem_top)
      simp at h
    simp [hs]
  have hfdeg : 0 < f.totalDegree := by
    by_contra! h
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hc : f.coeff 0 ≠ 0 := by
      intro hc
      apply hf
      rw [he, hc, map_zero]
      exact I.zero_mem
    have hu : IsUnit f := by rw [he]; exact (isUnit_iff_ne_zero.mpr hc).map C
    apply hJ
    dsimp [J]
    rw [Ideal.span_singleton_eq_top.mpr hu, sup_top_eq]
  obtain ⟨e, _, hed, hedim, helc⟩ := principal_section_degree_budget I d hdim hdegree f hf hfdeg hJ
  have hh := pure_ideal_grid_card_le n J m e hedim helc
    (principal_section_minimalPrimeComponents_pure I hdim f hf) S s hzJ hgrid
  exact hh.trans (Nat.mul_le_mul_right _ hed)

end
end AffineCurveCounting
