/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Funext

/-! The Zariski topology on field-valued affine points, induced by their
evaluation prime ideals. Polynomial vanishing characterizes closure;
a nonzero principal open is dense over any infinite field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The prime ideal of polynomials vanishing at the affine point `x`, as a point of the prime
spectrum of `MvPolynomial σ K`. -/
def affineEvaluationPrime {K σ : Type*} [Field K] (x : σ → K) :
    PrimeSpectrum (MvPolynomial σ K) :=
  ⟨RingHom.ker (eval x),RingHom.ker_isPrime (eval x)⟩

/-- The Zariski topology on the affine points `σ → K`, induced from the prime spectrum of
`MvPolynomial σ K` via `affineEvaluationPrime`. -/
@[instance_reducible] def affinePointZariskiTopology (K σ : Type*) [Field K] :
    TopologicalSpace (σ → K) :=
  TopologicalSpace.induced affineEvaluationPrime inferInstance

attribute [local instance] affinePointZariskiTopology

/-- In the Zariski topology on affine points, `x` lies in the closure of `S` if and only if
every polynomial vanishing on `S` vanishes at `x`. -/
theorem affine_point_mem_closure_iff
    {K σ : Type*} [Field K] (S : Set (σ → K)) (x : σ → K) :
    x ∈ closure S ↔ ∀ p : MvPolynomial σ K,
      (∀ y ∈ S, eval y p = 0) → eval x p = 0 := by
  rw [(Topology.IsInducing.induced affineEvaluationPrime).closure_eq_preimage_closure_image,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hmem (p : MvPolynomial σ K) :
      p ∈ PrimeSpectrum.vanishingIdeal (affineEvaluationPrime '' S) ↔
        ∀ y ∈ S, eval y p = 0 := by
    rw [PrimeSpectrum.mem_vanishingIdeal]
    constructor
    · intro h y hy
      exact h _ ⟨y,hy,rfl⟩
    · intro h q hq
      obtain ⟨y,hy,rfl⟩ := hq
      exact h y hy
  change (∀ p ∈ PrimeSpectrum.vanishingIdeal (affineEvaluationPrime '' S), eval x p = 0) ↔ _
  simp only [hmem]

private theorem affine_point_dense_of_vanishing
    {K σ : Type*} [Field K] (S : Set (σ → K))
    (hS : ∀ p : MvPolynomial σ K, (∀ y ∈ S, eval y p = 0) → p = 0) :
    Dense S := by
  intro x
  rw [affine_point_mem_closure_iff]
  intro p hp
  rw [hS p hp,map_zero]

/-- Over an infinite field, the nonvanishing locus of a nonzero polynomial is Zariski dense in
the affine points. -/
theorem affine_principal_open_dense
    {K σ : Type*} [Field K] [Infinite K] (p : MvPolynomial σ K) (hp : p ≠ 0) :
    Dense {x : σ → K | eval x p ≠ 0} := by
  apply affine_point_dense_of_vanishing
  intro q hq
  have hpq : p * q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_mul,map_zero]
    by_cases hx : eval x p = 0
    · rw [hx,zero_mul]
    · rw [hq x hx,mul_zero]
  exact (mul_eq_zero.mp hpq).resolve_left hp

private theorem affine_polynomial_zero_set_closed
    {K σ : Type*} [Field K] (p : MvPolynomial σ K) :
    IsClosed {x : σ → K | eval x p = 0} := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [affine_point_mem_closure_iff] at hx
  exact hx p (fun _ h => h)

/-- The nonvanishing locus of a polynomial is Zariski open in the affine points. -/
theorem affine_polynomial_nonzero_set_open
    {K σ : Type*} [Field K] (p : MvPolynomial σ K) :
    IsOpen {x : σ → K | eval x p ≠ 0} :=
  (affine_polynomial_zero_set_closed p).isOpen_compl

end
end CCDN
