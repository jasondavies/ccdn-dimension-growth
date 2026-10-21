/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Hilbert.FilteredComponentRank
import CCDN.Hilbert.PolynomialComparison
import Mathlib.Algebra.BigOperators.Field

/-! The total multiplicity of the minimal-prime components of a
pure-dimensional affine ideal is at most the original Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The leading terms of same-dimensional minimal-prime components are
bounded by the original leading term. -/
private theorem minimalPrimeComponents_leadingCoeff_sum_le
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (m : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m) :
    (∑ P : minimalPrimeComponents I, (filteredHilbertPolynomial P.val).leadingCoeff) ≤
      (filteredHilbertPolynomial I).leadingCoeff := by
  classical
  have hIpos := filteredHilbertPolynomial_leadingCoeff_pos I hI
  rcases isEmpty_or_nonempty (minimalPrimeComponents I) with hempty | hnonempty
  · let := hempty
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hIpos.le
  let := hnonempty
  have hpos (P : minimalPrimeComponents I) :
      0 < (filteredHilbertPolynomial P.val).leadingCoeff :=
    filteredHilbertPolynomial_leadingCoeff_pos P.val
      (minimalPrimeComponents_isPrime P.property).ne_top
  have hsumpos :
      0 < ∑ P : minimalPrimeComponents I, (filteredHilbertPolynomial P.val).leadingCoeff := by
    exact Finset.sum_pos (fun P _ => hpos P) Finset.univ_nonempty
  obtain ⟨D, hD⟩ := minimalPrimeComponents_filtered_rank_lower I
  let P := ∑ J : minimalPrimeComponents I, filteredHilbertPolynomial J.val
  let Q := (filteredHilbertPolynomial I).comp (Polynomial.X + Polynomial.C (D : ℚ))
  have hPcoeff : P.coeff m =
      ∑ J : minimalPrimeComponents I, (filteredHilbertPolynomial J.val).leadingCoeff := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.leadingCoeff, hpure]
  have hPdeg : P.natDegree = m := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro J _
      exact (hpure J).le
    · rw [hPcoeff]
      exact ne_of_gt hsumpos
  have hPlc : P.leadingCoeff =
      ∑ J : minimalPrimeComponents I, (filteredHilbertPolynomial J.val).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hPdeg, hPcoeff]
  have hQdeg : Q.natDegree = m := by
    simp only [Q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hdim]
  have hQlc : Q.leadingCoeff = (filteredHilbertPolynomial I).leadingCoeff := by
    dsimp only [Q]
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hPlcpos : 0 < P.leadingCoeff := hPlc.symm ▸ hsumpos
  have hQlcpos : 0 < Q.leadingCoeff := hQlc.symm ▸ hIpos
  have hle : ∃ N : ℕ, ∀ n ≥ N, P.eval (n : ℚ) ≤ Q.eval (n : ℚ) := by
    obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
    choose N hN using fun J : minimalPrimeComponents I => filteredHilbertPolynomial_spec J.val
    refine ⟨max M (Finset.univ.sup N), fun n hn => ?_⟩
    have hcomponents (J : minimalPrimeComponents I) :
        (filteredHilbertPolynomial J.val).eval (n : ℚ) =
          (Module.finrank K (filteredCoordinateSpace J.val n) : ℚ) :=
      hN J n ((Finset.le_sup (Finset.mem_univ J)).trans ((le_max_right _ _).trans hn))
    simp only [P, Q, Polynomial.eval_finsetSum, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, hcomponents]
    rw [show (n : ℚ) + D = ((D + n : ℕ) : ℚ) by push_cast; ring,
      hM (D + n) (by omega)]
    exact_mod_cast hD n
  have hh := polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hPlcpos hQlcpos
    (hPdeg.trans hQdeg.symm) hle
  simpa only [hPlc, hQlc] using hh

/-- The integer degree budget for pure-dimensional minimal-prime components. -/
private theorem minimalPrimeComponents_multiplicity_sum_le
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (m d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m)
    (δ : minimalPrimeComponents I → ℕ)
    (hδ : ∀ P, (filteredHilbertPolynomial P.val).leadingCoeff = (δ P : ℚ) / m.factorial) :
    ∑ P, δ P ≤ d := by
  have hh := minimalPrimeComponents_leadingCoeff_sum_le I hI m hdimdeg.natDegree_eq hpure
  simp only [hδ, hdimdeg.leadingCoeff_eq, ← Finset.sum_div] at hh
  have hfac : (0 : ℚ) < m.factorial := by positivity
  exact_mod_cast (div_le_div_iff_of_pos_right hfac).mp hh

/-- Positive integral component multiplicities exist and satisfy the budget. -/
theorem exists_minimalPrimeComponents_multiplicity_budget
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (m d : ℕ)
    (hdimdeg : HasAffineDimensionDegree I m d)
    (hpure : ∀ P : minimalPrimeComponents I,
      (filteredHilbertPolynomial P.val).natDegree = m) :
    ∃ δ : minimalPrimeComponents I → ℕ,
      (∀ P, 0 < δ P ∧
        (filteredHilbertPolynomial P.val).leadingCoeff = (δ P : ℚ) / m.factorial) ∧
      ∑ P, δ P ≤ d := by
  have hex (P : minimalPrimeComponents I) :
      ∃ e : ℕ, 0 < e ∧
        (filteredHilbertPolynomial P.val).leadingCoeff = (e : ℚ) / m.factorial := by
    obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity P.val
      (minimalPrimeComponents_isPrime P.property).ne_top
    exact ⟨e, he, by simpa only [hpure P] using hlc⟩
  choose δ hδpos hδ using hex
  exact ⟨δ, fun P => ⟨hδpos P, hδ P⟩,
    minimalPrimeComponents_multiplicity_sum_le I hI m d hdimdeg hpure δ hδ⟩

end
end CCDN
