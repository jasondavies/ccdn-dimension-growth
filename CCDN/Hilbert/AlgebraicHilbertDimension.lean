/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.HilbertTranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Affine Hilbert dimension across algebraic coefficient extensions.
Integral embeddings transfer a constructed transcendence basis; algebraic
extension of the coefficient field preserves its cardinality. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem algebraic_polynomial_extension_integral
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    (map (σ := σ) (algebraMap k K)).IsIntegral := by
  change ∀ f : MvPolynomial σ K, IsIntegral (MvPolynomial σ k) f
  intro f
  induction f using MvPolynomial.induction_on with
  | C c =>
    apply IsIntegral.map_of_comp_eq (C : k →+* MvPolynomial σ k)
      (C : K →+* MvPolynomial σ K) (by ext a; simp)
    exact isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic c)
  | add f g hf hg => exact hf.add hg
  | mul_X f i hf =>
    apply hf.mul
    simpa only [algebraMap_def, map_X] using
      (isIntegral_algebraMap (R := MvPolynomial σ k) (A := MvPolynomial σ K) (x := X i))

theorem algebraic_coefficient_integral_embedding_hilbert_dimension_eq
    {k K σ τ : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (J : Ideal (MvPolynomial τ K)) [J.IsPrime]
    (ψ : (MvPolynomial σ k ⧸ I) →ₐ[k] (MvPolynomial τ K ⧸ J))
    (hψ : Function.Injective ψ) (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial I).natDegree = (filteredHilbertPolynomial J).natDegree := by
  classical
  let A := MvPolynomial σ k ⧸ I
  let B := MvPolynomial τ K ⧸ J
  let : Algebra A B := ψ.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom ψ
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  let : Algebra.IsIntegral A B := ⟨hint⟩
  let : Algebra.IsAlgebraic A B :=
    ⟨fun x => (show IsIntegral A x from hint x).isAlgebraic⟩
  obtain ⟨U, hU, hBU⟩ := exists_hilbert_coordinate_transcendence_basis I
  have hb := hBU.algebraMap_comp (A := B)
  have hbK := (Algebra.IsAlgebraic.isTranscendenceBasis_iff k K).mp hb
  have hJ := hilbert_dimension_eq_transcendence_basis_card J _ hbK
  rw [Nat.card_eq_fintype_card] at hU
  exact hU.symm.trans hJ.symm

/-- A prime over the original ideal has the same Hilbert dimension
after an algebraic coefficient extension. -/
theorem algebraic_polynomial_prime_hilbert_dimension
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (hP : P.comap (map (algebraMap k K)) = I) :
    (filteredHilbertPolynomial P).natDegree = (filteredHilbertPolynomial I).natDegree := by
  subst I
  let φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ K :=
    mapAlgHom (Algebra.ofId k K)
  let ψ := Ideal.quotientMapₐ P φ le_rfl
  have hψ : Function.Injective ψ := Ideal.quotientMap_injective
  have hint : ψ.IsIntegral := (algebraic_polynomial_extension_integral k K σ).quotient
  exact (algebraic_coefficient_integral_embedding_hilbert_dimension_eq _ P ψ hψ hint).symm

/-- All minimal components of an extended prime ideal have the
original dimension. -/
theorem algebraic_polynomial_minimalPrime_under
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (P : Ideal (MvPolynomial σ K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes) :
    P.comap (map (algebraMap k K)) = I := by
  have : P.IsPrime := hP.isPrime
  let : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ K) :=
    ⟨algebraic_polynomial_extension_integral k K σ⟩
  have hIP : I ≤ P.under (MvPolynomial σ k) := Ideal.map_le_iff_le_comap.mp hP.le
  obtain ⟨Q, hQP, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := I) (q := P.under (MvPolynomial σ k)) P hIP
  have hIQ : I.map (map (algebraMap k K)) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (by
      simpa only [Ideal.under_def, algebraMap_def] using hQover.over.le)
  have hPQ : P ≤ Q := hP.2 ⟨hQprime, hIQ⟩ hQP
  have he : P = Q := le_antisymm hPQ hQP
  rw [he]
  simpa only [Ideal.under_def, algebraMap_def] using hQover.over.symm

theorem algebraic_polynomial_minimalPrime_dimension
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (P : Ideal (MvPolynomial σ K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes) :
    (filteredHilbertPolynomial P).natDegree = (filteredHilbertPolynomial I).natDegree := by
  have : P.IsPrime := hP.isPrime
  exact algebraic_polynomial_prime_hilbert_dimension k K σ I P
    (algebraic_polynomial_minimalPrime_under k K σ I P hP)

end
end CCDN
