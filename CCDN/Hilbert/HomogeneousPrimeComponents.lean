/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealScalarDescent
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import CCDN.Algebra.PolynomialPredicates
/-! Homogeneity survives coefficient extension and passage to
minimal-prime components. The latter uses the prime homogeneous core. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientLinearPolynomial_homogeneousComponent
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (φ : K →ₗ[k] k) (N : ℕ) (f : MvPolynomial (Fin n) K) :
    coefficientLinearPolynomial φ (homogeneousComponent N f) =
      homogeneousComponent N (coefficientLinearPolynomial φ f) := by
  ext a
  simp only [coefficientLinearPolynomial_coeff, coeff_homogeneousComponent]
  split_ifs <;> simp only [map_zero]

/-- The extension of scalars of a homogeneous ideal is homogeneous. -/
theorem homogeneous_ideal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : IsHomogeneousIdeal I) :
    ∀ f ∈ I.map (map (algebraMap K L)), ∀ N,
      homogeneousComponent N f ∈ I.map (map (algebraMap K L)) := by
  intro f hf N
  by_contra hn
  obtain ⟨φ, hφ⟩ := exists_coefficientLinearPolynomial_not_mem I _ hn
  apply hφ
  rw [coefficientLinearPolynomial_homogeneousComponent]
  exact hI _ (coefficientLinearPolynomial_mem_scalar_extension I f hf φ) N

theorem minimal_prime_ideal_homogeneous
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (P : Ideal (MvPolynomial σ K)) (hP : P ∈ I.minimalPrimes) :
    IsHomogeneousIdeal P := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  let G := homogeneousSubmodule σ K
  let C := (P.homogeneousCore G).toIdeal
  have hCprime : C.IsPrime := hP.isPrime.homogeneousCore (𝒜 := G)
  have hCI : I ≤ C := by
    intro f hf
    rw [← sum_homogeneousComponent f]
    apply C.sum_mem
    intro N _
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem G (homogeneousComponent N f) from
        ⟨N, homogeneousComponent_mem N f⟩) (hP.le (hI f hf N))
  have hCP : C ≤ P := Ideal.toIdeal_homogeneousCore_le G P
  have hPC : P ≤ C := hP.2 ⟨hCprime, hCI⟩ hCP
  intro f hf N
  exact hCP (homogeneousComponent_mem_of_mem
    (P.homogeneousCore G).isHomogeneous (hPC hf) N)

end
end CCDN
