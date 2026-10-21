/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.AuxiliaryPolynomial.HypersurfaceGoodDirection
import CCDN.AuxiliaryPolynomial.HypersurfacePositioning
import CCDN.Hilbert.FilteredHilbertEquiv
import CCDN.Hilbert.FullDimension
import CCDN.Hilbert.ProperHilbertDimension
import CCDN.Projection.BoundedLinearElimination
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.ForMathlib.MvPolynomial
/-! Homogeneous-linear Noether normalization over an infinite field.
The parameter forms, integrality and algebraic independence are constructed
from the prime ideal and its filtered Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_integral_linear_elimination_infinite
    {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (I : Ideal (MvPolynomial (Option σ) K))
    (f : MvPolynomial (Option σ) K) (hf : f ≠ 0) (hfi : f ∈ I) :
    ∃ a : σ → MvPolynomial (Option σ) K,
      (∀ i, (a i).IsHomogeneous 1) ∧ (projectionCoordinateMap I a).IsIntegral := by
  let P := X none * homogeneousComponent f.totalDegree f
  have hp : P ≠ 0 := mul_ne_zero (X_ne_zero none) (homogeneousComponent_totalDegree_ne_zero hf)
  have hhom : P.IsHomogeneous (1 + f.totalDegree) :=
    (isHomogeneous_X K none).mul (homogeneousComponent_isHomogeneous _ _)
  obtain ⟨b, hb⟩ : ∃ b : Option σ → K, eval b P ≠ 0 := by
    by_contra! hn
    exact hp (hhom.eq_zero_of_forall_eval_eq_zero hn)
  have hpval : b none * eval b (homogeneousComponent f.totalDegree f) ≠ 0 := by
    simpa only [P, eval_mul, eval_X] using hb
  have hb0 : b none ≠ 0 := left_ne_zero_of_mul hpval
  have hdir := right_ne_zero_of_mul hpval
  let a : σ → MvPolynomial (Option σ) K :=
    fun i => X (some i) - C (b (some i) / b none) * X none
  refine ⟨a, fun i => (isHomogeneous_X K (some i)).sub
    (isHomogeneous_C_mul_X _ none), ?_⟩
  have hint : (coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb0)).IsIntegral := by
    apply coordinateEliminationMap_isIntegral I _
      (normalizedHypersurfaceCoordinates 0 b hb0 f) _
      (normalizedHypersurfaceCoordinates_monic 0 b hb0 f hdir)
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hfi)
  have he : coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb0) =
      projectionCoordinateMap I a := by
    ext i
    rw [coordinateEliminationMap_direction_X]
    simp [projectionCoordinateMap, a]
  rwa [he] at hint

lemma exists_fin_integral_linear_elimination_infinite
    {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1) (hcodim : m < n) :
    ∃ a : Fin n → MvPolynomial (Fin (n + 1)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).natDegree = m + 1 := by
  classical
  let e := renameEquiv K (finSuccEquiv n)
  let : LinearOrder (Option (Fin n)) :=
    LinearOrder.lift' (finSuccEquiv n).symm (finSuccEquiv n).symm.injective
  let J := I.map e
  have : J.IsPrime := Ideal.map_isPrime_of_equiv e
  have hpoly : filteredHilbertPolynomial I = filteredHilbertPolynomial J :=
    filteredHilbertPolynomial_renameEquiv I (finSuccEquiv n)
  have hJ0 : J ≠ ⊥ := by
    intro hz
    rw [hz, filteredHilbertPolynomial_bot] at hpoly
    have hh := congrArg Polynomial.natDegree hpoly
    simp only [hdim, Polynomial.natDegree_preHilbertPoly, Fintype.card_option, Fintype.card_fin] at hh
    omega
  obtain ⟨f, hfI, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
  obtain ⟨b, hb, hint⟩ := exists_integral_linear_elimination_infinite J f hf hfI
  have hJ : J = I.map
      (e : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Option (Fin n)) K) := rfl
  let φ := (Ideal.quotientEquivAlg I J e hJ).symm
  let a : Fin n → MvPolynomial (Fin (n + 1)) K := fun i => e.symm (b i)
  have ha (i) : (a i).IsHomogeneous 1 := by
    change (rename (finSuccEquiv n).symm (b i)).IsHomogeneous 1
    rw [rename_eq_aeval]
    simpa only [Nat.one_mul, Function.comp_def] using
      (hb i).aeval (fun j => X ((finSuccEquiv n).symm j)) (fun j => isHomogeneous_X K _)
  have hφ : φ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ φ.surjective
  have hcomp := RingHom.IsIntegral.trans
    (projectionCoordinateMap J b).toRingHom φ.toRingHom hint hφ
  have he : φ.toAlgHom.comp (projectionCoordinateMap J b) = projectionCoordinateMap I a := by
    ext i
    simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    change φ (Ideal.Quotient.mk J (b i)) = Ideal.Quotient.mk I (a i)
    dsimp only [φ]
    rw [Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
  change (φ.toAlgHom.comp (projectionCoordinateMap J b)).IsIntegral at hcomp
  rw [he] at hcomp
  exact ⟨a, ha, hcomp, (integral_projection_hilbert_dimension_eq I _ hcomp).trans hdim⟩

theorem exists_linear_integral_normalization_infinite
    {K : Type*} [Field K] [Infinite K] (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + 1 + k)) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1) :
    ∃ a : Fin (m + 1) → MvPolynomial (Fin (m + 1 + k)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I a) := by
  induction k with
  | zero =>
    let a : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K := X
    have he : projectionCoordinateMap I a = Ideal.Quotient.mkₐ K I := by
      ext i
      simp [projectionCoordinateMap, a]
    have hI0 : I = ⊥ := ideal_eq_bot_of_full_hilbert_dimension I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›) (by simpa only [Fintype.card_fin] using hdim)
    refine ⟨a, fun i => isHomogeneous_X K i, ?_, ?_⟩
    · rw [he]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective K I)
    · rw [he]
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      change RingHom.ker ((Ideal.Quotient.mkₐ K I) :
        MvPolynomial (Fin (m + 1)) K →+* MvPolynomial (Fin (m + 1)) K ⧸ I) = ⊥
      rwa [Ideal.Quotient.mkₐ_ker]
  | succ k ih =>
    obtain ⟨c, hc, hintc, hdimJ⟩ :=
      exists_fin_integral_linear_elimination_infinite (n := m + 1 + k) I hdim (by omega)
    let ψ := projectionCoordinateMap I c
    let J := RingHom.ker ψ
    have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
    obtain ⟨a, ha, hinta, hinja⟩ := ih J hdimJ
    let a' : Fin (m + 1) → MvPolynomial (Fin (m + 1 + (k + 1))) K :=
      fun i => aeval c (a i)
    let φ := Ideal.kerLiftAlg ψ
    have hφ : φ.IsIntegral := hintc.kerLift
    have hcomp := RingHom.IsIntegral.trans
      (projectionCoordinateMap J a).toRingHom φ.toRingHom hinta hφ
    have he : φ.comp (projectionCoordinateMap J a) = projectionCoordinateMap I a' := by
      ext i
      simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      rfl
    refine ⟨a', fun i => ?_, ?_, ?_⟩
    · simpa only [Nat.one_mul] using (ha i).aeval c hc
    · change (φ.comp (projectionCoordinateMap J a)).IsIntegral at hcomp
      rwa [he] at hcomp
    · rw [← he]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja

theorem exists_linear_integral_normalization_infinite_of_le
    {K : Type*} [Field K] [Infinite K] (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1) :
    ∃ a : Fin (m + 1) → MvPolynomial (Fin n) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact exists_linear_integral_normalization_infinite m k I hdim

end
end CCDN
