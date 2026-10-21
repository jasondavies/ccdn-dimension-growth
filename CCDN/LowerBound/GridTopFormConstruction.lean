/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.HomogeneousLinearDescent
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! Explicit grid equations whose highest homogeneous part is absolutely
irreducible. The top form y*z^(d-1)-x^d is primitive and linear in y. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma homogeneousComponent_mul_of_degree_le {R σ : Type*} [CommRing R]
    (f g : MvPolynomial σ R) {a b : ℕ}
    (hf : f.totalDegree ≤ a) (hg : g.totalDegree ≤ b) :
    homogeneousComponent (a + b) (f * g) =
      homogeneousComponent a f * homogeneousComponent b g := by
  by_cases hfa : f.totalDegree = a
  · by_cases hgb : g.totalDegree = b
    · rw [← hfa, ← hgb, top_homogeneousComponent_mul]
    · have hglt : g.totalDegree < b := by omega
      rw [homogeneousComponent_eq_zero _ _ hglt, mul_zero]
      apply homogeneousComponent_eq_zero
      have h := totalDegree_mul f g
      omega
  · have hflt : f.totalDegree < a := by omega
    rw [homogeneousComponent_eq_zero _ _ hflt, zero_mul]
    apply homogeneousComponent_eq_zero
    have h := totalDegree_mul f g
    omega

/-- The monic polynomial in one chosen variable vanishing on s. -/
def variableGridPolynomial {R σ : Type*} [CommRing R] (s : Finset R) (i : σ) :
    MvPolynomial σ R := ∏ a ∈ s, (X i - C a)

private lemma variableGridPolynomial_totalDegree_le {R σ : Type*} [CommRing R]
    (s : Finset R) (i : σ) : (variableGridPolynomial s i).totalDegree ≤ s.card := by
  unfold variableGridPolynomial
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ a ∈ s, (X i - C a : MvPolynomial σ R).totalDegree ≤ ∑ _a ∈ s, 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact (totalDegree_sub _ _).trans
        (by simp only [totalDegree_C, max_zero]; exact (isHomogeneous_X R i).totalDegree_le)
    _ = _ := by simp

private lemma variableGridPolynomial_top {R σ : Type*} [CommRing R]
    (s : Finset R) (i : σ) :
    homogeneousComponent s.card (variableGridPolynomial s i) = X i ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [variableGridPolynomial, homogeneousComponent_zero]
  | @insert a s ha ih =>
    have hfactor : (X i - C a : MvPolynomial σ R).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans
        (by simp only [totalDegree_C, max_zero]; exact (isHomogeneous_X R i).totalDegree_le)
    have htop : homogeneousComponent 1 (X i - C a : MvPolynomial σ R) = X i := by
      rw [map_sub, homogeneousComponent_eq_self (isHomogeneous_X R i),
        homogeneousComponent_eq_zero _ _ (by simp), sub_zero]
    simp only [variableGridPolynomial, Finset.prod_insert ha, Finset.card_insert_of_notMem ha] at ⊢
    change homogeneousComponent (s.card + 1) ((X i - C a) * variableGridPolynomial s i) = _
    rw [Nat.add_comm s.card 1,
      homogeneousComponent_mul_of_degree_le _ _ hfactor (variableGridPolynomial_totalDegree_le s i),
      htop]
    change X i * homogeneousComponent s.card (variableGridPolynomial s i) = _
    rw [ih, pow_add, pow_one]

/-- Raise the degree while preserving the specified grid roots. -/
def paddedGridPolynomial {R σ : Type*} [CommRing R] (s : Finset R) (i : σ) (d : ℕ) :
    MvPolynomial σ R := X i ^ (d - s.card) * variableGridPolynomial s i

private lemma paddedGridPolynomial_totalDegree_le {R σ : Type*} [CommRing R]
    (s : Finset R) (i : σ) {d : ℕ} (hd : s.card ≤ d) :
    (paddedGridPolynomial s i d).totalDegree ≤ d := by
  apply (totalDegree_mul _ _).trans
  have hp : (X i ^ (d - s.card) : MvPolynomial σ R).totalDegree ≤ d - s.card := by
    exact (totalDegree_pow _ _).trans
      (by simpa using Nat.mul_le_mul_left (d - s.card) (isHomogeneous_X R i).totalDegree_le)
  have hg := variableGridPolynomial_totalDegree_le s i
  omega

private lemma paddedGridPolynomial_top {R σ : Type*} [CommRing R]
    (s : Finset R) (i : σ) {d : ℕ} (hd : s.card ≤ d) :
    homogeneousComponent d (paddedGridPolynomial s i d) = X i ^ d := by
  have he : d = (d - s.card) + s.card := (Nat.sub_add_cancel hd).symm
  unfold paddedGridPolynomial
  nth_rw 1 [he]
  rw [homogeneousComponent_mul_of_degree_le _ _
    (isHomogeneous_X_pow i _).totalDegree_le (variableGridPolynomial_totalDegree_le s i),
    homogeneousComponent_eq_self (isHomogeneous_X_pow i _), variableGridPolynomial_top,
    ← pow_add, ← he]

private lemma paddedGridPolynomial_eval_zero {R σ : Type*} [CommRing R]
    (s : Finset R) (i : σ) (d : ℕ) (z : σ → R) (hz : z i ∈ s) :
    eval z (paddedGridPolynomial s i d) = 0 := by
  have hg : eval z (variableGridPolynomial s i) = 0 := by
    simp only [variableGridPolynomial, map_prod]
    apply Finset.prod_eq_zero hz
    simp
  simp [paddedGridPolynomial, hg]

/-- A degree-d binomial that is absolutely irreducible in every characteristic. -/
private def gridTopForm (R : Type*) [CommRing R] (d : ℕ) : MvPolynomial (Fin 3) R :=
  X 0 * X 2 ^ (d - 1) - X 1 ^ d

private lemma gridTopForm_irreducible {R : Type*} [Field R] (d : ℕ) :
    Irreducible (gridTopForm R d) := by
  have hrel : IsRelPrime (X (2 : Fin 3) : MvPolynomial (Fin 3) R) (X 1) := by
    apply (X_prime.irreducible.isRelPrime_iff_not_dvd).mpr
    simpa only [X_dvd_X] using (show (2 : Fin 3) ≠ 1 by decide)
  have hvars (j : Fin 3) (hj : j ≠ 0) (k : ℕ) :
      (0 : Fin 3) ∉ (X j ^ k : MvPolynomial (Fin 3) R).vars := by
    intro h
    have hh := vars_pow (X j : MvPolynomial (Fin 3) R) k h
    simp [vars_X, Ne.symm hj] at hh
  have h := irreducible_mul_X_add (X (2 : Fin 3) ^ (d - 1) : MvPolynomial (Fin 3) R)
    (-(X 1 ^ d)) 0 (pow_ne_zero _ (X_ne_zero _))
    (hvars 2 (by decide) _) (by simpa using hvars 1 (by decide) d) hrel.pow.neg_right
  rw [gridTopForm, mul_comm (X (0 : Fin 3)), sub_eq_add_neg]
  exact h

/-- A grid equation with the absolutely irreducible top form above. -/
def gridTopFormEquation {R : Type*} [CommRing R] (s : Finset R) (d : ℕ) :
    MvPolynomial (Fin 3) R :=
  X 0 * paddedGridPolynomial s 2 (d - 1) - paddedGridPolynomial s 1 d

private lemma gridTopFormEquation_totalDegree_le {R : Type*} [CommRing R]
    (s : Finset R) {d : ℕ} (hd : 1 ≤ d) (hs : s.card ≤ d - 1) :
    (gridTopFormEquation s d).totalDegree ≤ d := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    have h := paddedGridPolynomial_totalDegree_le s (2 : Fin 3) hs
    have hx := (isHomogeneous_X R (0 : Fin 3)).totalDegree_le
    omega
  · exact paddedGridPolynomial_totalDegree_le s 1 (by omega)

private lemma gridTopFormEquation_top {R : Type*} [CommRing R]
    (s : Finset R) {d : ℕ} (hd : 1 ≤ d) (hs : s.card ≤ d - 1) :
    homogeneousComponent d (gridTopFormEquation s d) = gridTopForm R d := by
  unfold gridTopFormEquation gridTopForm
  rw [map_sub, paddedGridPolynomial_top s 1 (by omega)]
  have he : d = 1 + (d - 1) := by omega
  nth_rw 1 [he]
  rw [homogeneousComponent_mul_of_degree_le _ _ (isHomogeneous_X R (0 : Fin 3)).totalDegree_le
    (paddedGridPolynomial_totalDegree_le s 2 hs),
    homogeneousComponent_eq_self (isHomogeneous_X R (0 : Fin 3)), paddedGridPolynomial_top s 2 hs]

lemma gridTopFormEquation_totalDegree {R : Type*} [CommRing R] [IsDomain R]
    (s : Finset R) {d : ℕ} (hd : 1 ≤ d) (hs : s.card ≤ d - 1) :
    (gridTopFormEquation s d).totalDegree = d := by
  apply le_antisymm (gridTopFormEquation_totalDegree_le s hd hs)
  by_contra h
  have hh := homogeneousComponent_eq_zero d (gridTopFormEquation s d) (by omega)
  rw [gridTopFormEquation_top s hd hs] at hh
  have hv := congrArg (eval (![0, 1, 0] : Fin 3 → R)) hh
  simp [gridTopForm] at hv

lemma gridTopFormEquation_eval_zero {R : Type*} [CommRing R]
    (s : Finset R) (d : ℕ) (z : Fin 3 → R) (h₁ : z 1 ∈ s) (h₂ : z 2 ∈ s) :
    eval z (gridTopFormEquation s d) = 0 := by
  simp only [gridTopFormEquation, map_sub, map_mul, eval_X,
    paddedGridPolynomial_eval_zero s 1 d z h₁,
    paddedGridPolynomial_eval_zero s 2 (d - 1) z h₂, mul_zero, sub_self]

private lemma gridTopForm_map {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (d : ℕ) : map φ (gridTopForm R d) = gridTopForm K d := by
  simp [gridTopForm]

/-- In particular, the integer grid equation satisfies the absolute
irreducibility condition imposed on the highest homogeneous part in Theorem 4. -/
theorem gridTopFormEquation_absolute_top (s : Finset ℤ) {d : ℕ}
    (hd : 1 ≤ d) (hs : s.card ≤ d - 1) :
    HasAbsIrreducibleTopForm (gridTopFormEquation s d) := by
  rw [HasAbsIrreducibleTopForm, AbsolutelyIrreducible, gridTopFormEquation_totalDegree s hd hs,
    gridTopFormEquation_top s hd hs, gridTopForm_map]
  exact gridTopForm_irreducible d

end
end CCDN
