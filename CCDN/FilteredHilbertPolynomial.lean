module

public import CCDN.StandardMonomials
public import CCDN.OrthantMultiplicity

/-! Existence, uniqueness and positive integral multiplicity of the
filtered Hilbert polynomial of a polynomial quotient, in arbitrary finite
dimension. These results construct the polynomial from standard exponents. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Classical

def standardExponentVectors {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) : Set (σ → ℕ) :=
  {a | Finsupp.equivFunOnFinite.symm a ∈ standardExponents I m}

lemma standardExponentVectors_lower {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) :
    IsLowerSet (standardExponentVectors I m) := by
  intro a b hab hb
  exact standardExponents_lower I m (fun i => hab i) hb

lemma standardExponentVectors_nonempty {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    (standardExponentVectors I MonomialOrder.degLex).Nonempty := by
  obtain ⟨r, hr, _, hmem⟩ := exists_standard_representative I 1
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, sub_zero] at hmem
    exact hI (Ideal.eq_top_of_isUnit_mem I hmem isUnit_one)
  obtain ⟨a, ha⟩ := support_nonempty.mpr hr0
  refine ⟨Finsupp.equivFunOnFinite a, ?_⟩
  change Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite a) ∈
    standardExponents I MonomialOrder.degLex
  rw [Equiv.symm_apply_apply]
  exact hr ha

lemma filteredCoordinateSpace_finrank_eq_vector_card {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Nat.card {a : σ → ℕ //
        a ∈ standardExponentVectors I MonomialOrder.degLex ∧ ∑ i, a i ≤ N} := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card]
  apply Nat.card_congr
  exact Finsupp.equivFunOnFinite.subtypeEquiv (fun a => by
    simp [boundedStandardExponents, standardExponentVectors, Finsupp.sum_fintype])

/-- Eventual polynomiality of the filtered coordinate-space dimension. -/
theorem filteredCoordinateSpace_eventually_polynomial {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) :
    ∃ P : Polynomial ℚ, ∃ N : ℕ, ∀ n ≥ N,
      P.eval (n : ℚ) = (Module.finrank K (filteredCoordinateSpace I n) : ℚ) := by
  obtain ⟨P, N, hN⟩ := lowerSet_eventually_polynomial
    (standardExponentVectors I MonomialOrder.degLex)
    (standardExponentVectors_lower I MonomialOrder.degLex)
  refine ⟨P, N, fun n hn => ?_⟩
  rw [filteredCoordinateSpace_finrank_eq_vector_card]
  exact hN n hn

lemma polynomial_eq_of_eventual_nat_eval_eq (P Q : Polynomial ℚ)
    (h : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  obtain ⟨N, hN⟩ := h
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨n, hn, rfl⟩
  exact hN n hn

/-- The uniquely determined filtered Hilbert polynomial. -/
def filteredHilbertPolynomial {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) : Polynomial ℚ :=
  (filteredCoordinateSpace_eventually_polynomial I).choose

theorem filteredHilbertPolynomial_spec {K σ : Type*} [Field K] [Fintype σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) :
    ∃ N : ℕ, ∀ n ≥ N, (filteredHilbertPolynomial I).eval (n : ℚ) =
      (Module.finrank K (filteredCoordinateSpace I n) : ℚ) :=
  (filteredCoordinateSpace_eventually_polynomial I).choose_spec

theorem filteredHilbertPolynomial_eq_of_eventual {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) =
      (Module.finrank K (filteredCoordinateSpace I n) : ℚ)) :
    filteredHilbertPolynomial I = P := by
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨M, hM⟩ := hP
  apply polynomial_eq_of_eventual_nat_eval_eq
  refine ⟨max N M, fun n hn => ?_⟩
  rw [hN n ((le_max_left _ _).trans hn), hM n ((le_max_right _ _).trans hn)]

/-- Proper polynomial quotients have a positive integer factorial-normalized
leading coefficient. Neither a Hilbert polynomial nor its degree is assumed. -/
theorem filteredHilbertPolynomial_positive_multiplicity {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    ∃ d : ℕ, 0 < d ∧
      (filteredHilbertPolynomial I).natDegree ≤ Fintype.card σ ∧
      (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial := by
  obtain ⟨P, d, hd, hdeg, hlc, N, hN⟩ := lowerSet_eventually_polynomial_positive
    (standardExponentVectors I MonomialOrder.degLex)
    (standardExponentVectors_lower I MonomialOrder.degLex)
    (standardExponentVectors_nonempty I hI)
  have he : filteredHilbertPolynomial I = P := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨N, fun n hn => ?_⟩
    rw [filteredCoordinateSpace_finrank_eq_vector_card]
    exact hN n hn
  exact ⟨d, hd, he.symm ▸ hdeg, he.symm ▸ hlc⟩

end
end CCDN
