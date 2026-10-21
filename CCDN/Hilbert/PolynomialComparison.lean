/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Polynomial.Basic

/-! Eventual inequalities compare the degree and leading coefficient of
Hilbert polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open Filter

lemma leadingCoeff_nonneg_of_eventual_nat_eval_nonneg (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  obtain ⟨N, hN⟩ := hP
  by_cases hd : P.natDegree = 0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hd
    rw [he, Polynomial.leadingCoeff_C]
    have hh := hN N le_rfl
    rw [he, Polynomial.eval_C] at hh
    exact hh
  · by_contra! hn
    have hdeg : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun n : ℕ => P.eval (n : ℚ)) atTop atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hn.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hneg⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot (0 : ℚ))).exists
    exact (not_lt_of_ge (hN n hnN)) hneg

lemma polynomial_natDegree_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff)
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  have hnon : 0 ≤ (Q - P).leadingCoeff := by
    apply leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    obtain ⟨N, hN⟩ := hle
    exact ⟨N, fun n hn => by simpa only [Polynomial.eval_sub, sub_nonneg] using hN n hn⟩
  by_contra! hd
  rw [Polynomial.leadingCoeff_sub_of_degree_lt' (Polynomial.degree_lt_degree hd)] at hnon
  linarith

lemma polynomial_leadingCoeff_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hd : P.natDegree = Q.natDegree)
    (hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hnon : 0 ≤ (Q - P).leadingCoeff := by
    apply leadingCoeff_nonneg_of_eventual_nat_eval_nonneg
    obtain ⟨N, hN⟩ := hle
    exact ⟨N, fun n hn => by simpa only [Polynomial.eval_sub, sub_nonneg] using hN n hn⟩
  by_contra! hc
  have hdeg : Q.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hQ)),
      Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hP)), hd]
  rw [Polynomial.leadingCoeff_sub_of_degree_eq hdeg (ne_of_lt hc)] at hnon
  linarith

lemma filteredHilbertPolynomial_leadingCoeff_pos {K σ : Type*} [Field K]
    [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    0 < (filteredHilbertPolynomial I).leadingCoeff := by
  obtain ⟨d, hd, _, he⟩ := filteredHilbertPolynomial_positive_multiplicity I hI
  rw [he]
  positivity

/-- Any filtered-dimension inequality between proper polynomial quotients
compares their Hilbert dimensions. -/
theorem filteredHilbertPolynomial_natDegree_le
    {K L σ τ : Type*} [Field K] [Field L] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L)) (hI : I ≠ ⊤)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).natDegree ≤ (filteredHilbertPolynomial J).natDegree := by
  apply polynomial_natDegree_le_of_eventual_nat_eval_le _ _
    (filteredHilbertPolynomial_leadingCoeff_pos I hI)
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
  refine ⟨max M N, fun n hn => ?_⟩
  rw [hM n ((le_max_left _ _).trans hn), hN n ((le_max_right _ _).trans hn)]
  exact_mod_cast hle n

/-- When dimensions agree, filtered comparison also compares the
leading coefficients, and hence the geometric multiplicities. -/
theorem filteredHilbertPolynomial_leadingCoeff_le
    {K L σ τ : Type*} [Field K] [Field L] [Fintype σ] [Fintype τ]
    [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L))
    (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    (hd : (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree)
    (hle : ∀ N, Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank L (filteredCoordinateSpace J N)) :
    (filteredHilbertPolynomial I).leadingCoeff ≤ (filteredHilbertPolynomial J).leadingCoeff := by
  apply polynomial_leadingCoeff_le_of_eventual_nat_eval_le _ _
    (filteredHilbertPolynomial_leadingCoeff_pos I hI)
    (filteredHilbertPolynomial_leadingCoeff_pos J hJ) hd
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec J
  refine ⟨max M N, fun n hn => ?_⟩
  rw [hM n ((le_max_left _ _).trans hn), hN n ((le_max_right _ _).trans hn)]
  exact_mod_cast hle n

end
end CCDN
