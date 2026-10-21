/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Weighted highest components through an auxiliary polynomial variable.
The Rees substitution keeps the original monomials as coefficients, so
its degree and leading coefficient record the weighted degree and top part. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private lemma finset_prod_polynomial_monomial {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (d : ι → ℕ) (a : ι → R) :
    (∏ i ∈ s, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [prod_insert hi, sum_insert hi, ih, Polynomial.monomial_mul_monomial]

def weightedDegreePolynomial {R σ : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C) (fun i => Polynomial.monomial (w i) (X i))

private lemma weightedDegreePolynomial_monomial {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) (m : σ →₀ ℕ) (a : R) :
    weightedDegreePolynomial w (monomial m a) =
      Polynomial.monomial (Finsupp.weight w m) (monomial m a) := by
  classical
  rw [weightedDegreePolynomial, eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.monomial_pow, Finsupp.prod]
  rw [finset_prod_polynomial_monomial, Polynomial.C_mul_monomial]
  congr 1
  · simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_comm]
  · exact (monomial_eq (s := m) (a := a)).symm

private lemma weightedDegreePolynomial_coeff {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) (f : MvPolynomial σ R) (k : ℕ) :
    (weightedDegreePolynomial w f).coeff k = weightedHomogeneousComponent w k f := by
  classical
  nth_rw 1 [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp only [weightedDegreePolynomial_monomial, Polynomial.coeff_monomial]
  rw [weightedHomogeneousComponent_apply, sum_filter]

lemma weighted_top_component_ne_zero {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) (f : MvPolynomial σ R) (hf : f ≠ 0) :
    weightedHomogeneousComponent w (f.weightedTotalDegree w) f ≠ 0 := by
  classical
  obtain ⟨m, hm, he⟩ := exists_mem_eq_sup f.support (support_nonempty.mpr hf) (Finsupp.weight w)
  intro hz
  have hh := congrArg (fun p : MvPolynomial σ R => p.coeff m) hz
  simp only [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hh
  have he' : Finsupp.weight w m = f.weightedTotalDegree w := he.symm
  rw [ite_eq_left he'] at hh
  exact (mem_support_iff.mp hm) hh

lemma weightedDegreePolynomial_natDegree {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) (f : MvPolynomial σ R) :
    (weightedDegreePolynomial w f).natDegree = f.weightedTotalDegree w := by
  by_cases hf : f = 0
  · simp [hf, weightedTotalDegree_zero]
  · apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [weightedDegreePolynomial_coeff]
      exact weightedHomogeneousComponent_eq_zero k f hk
    · rw [weightedDegreePolynomial_coeff]
      exact weighted_top_component_ne_zero w f hf

private lemma weightedDegreePolynomial_ne_zero {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) {f : MvPolynomial σ R} (hf : f ≠ 0) :
    weightedDegreePolynomial w f ≠ 0 := by
  intro hz
  have hh := congrArg (fun P => Polynomial.coeff P (f.weightedTotalDegree w)) hz
  rw [weightedDegreePolynomial_coeff, Polynomial.coeff_zero] at hh
  exact weighted_top_component_ne_zero w f hf hh

private lemma weightedDegreePolynomial_leadingCoeff {R σ : Type*} [CommSemiring R]
    (w : σ → ℕ) (f : MvPolynomial σ R) :
    (weightedDegreePolynomial w f).leadingCoeff =
      weightedHomogeneousComponent w (f.weightedTotalDegree w) f := by
  rw [Polynomial.leadingCoeff, weightedDegreePolynomial_natDegree, weightedDegreePolynomial_coeff]

lemma weightedTotalDegree_mul_of_ne_zero {R σ : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).weightedTotalDegree w = f.weightedTotalDegree w + g.weightedTotalDegree w := by
  rw [← weightedDegreePolynomial_natDegree, map_mul,
    Polynomial.natDegree_mul (weightedDegreePolynomial_ne_zero w hf)
      (weightedDegreePolynomial_ne_zero w hg),
    weightedDegreePolynomial_natDegree, weightedDegreePolynomial_natDegree]

lemma weighted_top_component_mul {R σ : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (f g : MvPolynomial σ R) :
    weightedHomogeneousComponent w ((f * g).weightedTotalDegree w) (f * g) =
      weightedHomogeneousComponent w (f.weightedTotalDegree w) f *
        weightedHomogeneousComponent w (g.weightedTotalDegree w) g := by
  rw [← weightedDegreePolynomial_leadingCoeff, map_mul, Polynomial.leadingCoeff_mul,
    weightedDegreePolynomial_leadingCoeff, weightedDegreePolynomial_leadingCoeff]

lemma weightedTotalDegree_zero_isUnit {K σ : Type*} [Field K]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (f : MvPolynomial σ K)
    (hf : f ≠ 0) (hd : f.weightedTotalDegree w = 0) : IsUnit f := by
  have hhom : f.IsWeightedHomogeneous w 0 :=
    isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero.mpr hd
  have he : f = C (f.coeff 0) := calc
    f = weightedHomogeneousComponent w 0 f := hhom.weightedHomogeneousComponent_same.symm
    _ = _ := weightedHomogeneousComponent_zero f (fun i => (hw i).ne')
  rw [he] at hf ⊢
  exact (isUnit_iff_ne_zero.mpr (C_eq_zero.not.mp hf)).map C

end
end CCDN
