/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Projection.IntegralProjectionHilbert
import CCDNPaper.Projection.LinearNormalizationInfinite
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral polynomial parameters vanishing on a finite grid.
Their degrees are bounded by the grid side length, independently of the
ambient number of coordinates and of the defining ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def gridCoordinatePolynomial {K σ : Type*} [Field K]
    (S : Finset K) (i : σ) : MvPolynomial σ K := ∏ t ∈ S, (X i - C t)

private lemma gridCoordinatePolynomial_degree {K σ : Type*} [Field K]
    (S : Finset K) (i : σ) : (gridCoordinatePolynomial S i).totalDegree ≤ S.card := by
  classical
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ t ∈ S, (X i - C t : MvPolynomial σ K).totalDegree) ≤ ∑ _t ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro t _
      exact (totalDegree_sub _ _).trans (by simp)
    _ = _ := by simp

private lemma gridCoordinatePolynomial_eval_zero {K σ : Type*} [Field K]
    (S : Finset K) (x : σ → K) (i : σ) (hxi : x i ∈ S) :
    eval x (gridCoordinatePolynomial S i) = 0 := by
  classical
  rw [gridCoordinatePolynomial, map_prod]
  apply Finset.prod_eq_zero hxi
  simp

/-- The coordinate grid polynomials give an integral map into every
quotient of the polynomial ring. This is proved using their monic equations. -/
private theorem gridCoordinateMap_isIntegral {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (S : Finset K) (hS : S.Nonempty) :
    (projectionCoordinateMap I (gridCoordinatePolynomial S)).IsIntegral := by
  classical
  let R := MvPolynomial σ K
  let A := MvPolynomial σ K ⧸ I
  let ψ := projectionCoordinateMap I (gridCoordinatePolynomial S)
  let : Algebra R A := ψ.toRingHom.toAlgebra
  have hC (c : K) : algebraMap R A (C c) = Ideal.Quotient.mk I (C c) := by
    change ψ (C c) = _
    simp only [ψ, projectionCoordinateMap, AlgHom.comp_apply, aeval_C]
    rfl
  let b : σ → A := fun i => Ideal.Quotient.mk I (X i)
  have hX (i : σ) : IsIntegral R (b i) := by
    let p : Polynomial R := ∏ t ∈ S, (Polynomial.X - Polynomial.C (C t))
    have hp : p.Monic := Polynomial.monic_prod_of_monic _ _
      (fun t _ => Polynomial.monic_X_sub_C _)
    have hdeg : p.natDegree = S.card := Polynomial.natDegree_finsetProd_X_sub_C_eq_card S C
    have hmon : (p - Polynomial.C (X i)).Monic := hp.sub_of_left (by
      apply Polynomial.degree_C_lt.trans_le
      rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]
      exact_mod_cast Finset.card_pos.mpr hS)
    refine ⟨p - Polynomial.C (X i), hmon, ?_⟩
    change Polynomial.aeval (b i) (p - Polynomial.C (X i)) = 0
    simp only [map_sub, Polynomial.aeval_C, p, map_prod, Polynomial.aeval_X, hC]
    change (∏ t ∈ S, (Ideal.Quotient.mk I (X i) - Ideal.Quotient.mk I (C t))) -
      ψ (X i) = 0
    simp only [ψ, projectionCoordinateMap, AlgHom.comp_apply, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk, gridCoordinatePolynomial, map_prod, map_sub, sub_self]
  intro a
  change IsIntegral R a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [← hC]
    exact isIntegral_algebraMap
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | mul_X f i hf => simpa only [map_mul] using hf.mul (hX i)

/-- Construct all polynomial parameters needed for a sharp grid count.
Each is zero on the entire grid, has degree at most its side length, and
together they give an injective integral polynomial-algebra map. -/
theorem exists_grid_polynomial_normalization
    {K : Type*} [Field K] [Infinite K] (n m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (S : Finset K) (hS : S.Nonempty) :
    ∃ l : Fin (m + 1) → MvPolynomial (Fin n) K,
      (∀ i, (l i).totalDegree ≤ S.card) ∧
      (projectionCoordinateMap I l).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I l) ∧
      (∀ x : Fin n → K, (∀ j, x j ∈ S) → ∀ i, eval x (l i) = 0) := by
  classical
  let g : Fin n → MvPolynomial (Fin n) K := gridCoordinatePolynomial S
  let ψ := projectionCoordinateMap I g
  let J := RingHom.ker ψ
  have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  have hint : ψ.IsIntegral := gridCoordinateMap_isIntegral I S hS
  have hdimJ : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq I ψ hint).trans hdim
  have hmn : m + 1 ≤ n := by
    obtain ⟨_, _, hh, _⟩ := filteredHilbertPolynomial_positive_multiplicity J (RingHom.ker_ne_top _)
    simpa only [hdimJ, Fintype.card_fin] using hh
  obtain ⟨a, ha, hinta, hinja⟩ :=
    exists_linear_integral_normalization_infinite_of_le m n hmn J hdimJ
  let l : Fin (m + 1) → MvPolynomial (Fin n) K := fun i => aeval g (a i)
  let φ := Ideal.kerLiftAlg ψ
  have hφ : φ.IsIntegral := hint.kerLift
  have he : φ.comp (projectionCoordinateMap J a) = projectionCoordinateMap I l := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  have hintl := RingHom.IsIntegral.trans (projectionCoordinateMap J a).toRingHom
    φ.toRingHom hinta hφ
  change (φ.comp (projectionCoordinateMap J a)).IsIntegral at hintl
  rw [he] at hintl
  refine ⟨l, fun i => ?_, hintl, ?_, ?_⟩
  · exact (aeval_totalDegree_le g (gridCoordinatePolynomial_degree S) (a i)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left S.card (ha i).totalDegree_le)
  · rw [← he]
    exact (Ideal.kerLiftAlg_injective ψ).comp hinja
  · intro x hx i
    change eval x (aeval g (a i)) = 0
    change (aeval x) (aeval g (a i)) = 0
    rw [comp_aeval_apply]
    change eval (fun j => eval x (g j)) (a i) = 0
    have hzero : (fun j => eval x (g j)) = 0 := by
      funext j
      exact gridCoordinatePolynomial_eval_zero S x j (hx j)
    rw [hzero, eval_zero]
    exact (ha i).coeff_eq_zero (by simp)

end
end CCDN
