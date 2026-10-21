/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialLinearDescent
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.BigOperators

/-! Coefficient-linear descent for arbitrary polynomial variable types.
A finite expansion in a coefficient-field basis proves exact ideal descent,
including nested-polynomial substitutions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

/-- Every polynomial over the extension is a finite sum of base-field
polynomials obtained by its basis-coordinate functionals. -/
private theorem polynomial_coefficient_basis_expansion {K L σ ι : Type*}
    [Field K] [Field L] [Algebra K L]
    (b : Basis ι K L) (g : MvPolynomial σ L) :
    ∃ s : Finset ι,
      g = ∑ i ∈ s, C (b i) *
        map (algebraMap K L) (polynomialCoefficientLinear (b.coord i) g) := by
  classical
  let s := g.support.biUnion (fun e => (b.repr (g.coeff e)).support)
  refine ⟨s, ?_⟩
  ext e
  simp only [coeff_sum, coeff_C_mul, coeff_map, polynomialCoefficientLinear_coeff]
  have hb := b.linearCombination_repr (g.coeff e)
  change (b.repr (g.coeff e)).sum (fun i c => c • b i) = g.coeff e at hb
  by_cases he : e ∈ g.support
  · have hsub : (b.repr (g.coeff e)).support ⊆ s := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨e, he, hi⟩
    calc
      g.coeff e = ∑ i ∈ (b.repr (g.coeff e)).support, (b.repr (g.coeff e)) i • b i := hb.symm
      _ = ∑ i ∈ s, (b.repr (g.coeff e)) i • b i := by
        apply Finset.sum_subset hsub
        intro i _ hi
        simp only [Finsupp.notMem_support_iff.mp hi, zero_smul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Basis.coord_apply, Algebra.smul_def, mul_comm]
  · have hz : g.coeff e = 0 := notMem_support_iff.mp he
    simp [hz]

/-- Exact membership in the scalar-extended ideal is detected by all
coefficient-linear functionals. -/
theorem mem_scalar_extension_iff_polynomialCoefficientLinear {K L σ : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ L) :
    g ∈ I.map (map (algebraMap K L)) ↔
      ∀ φ : L →ₗ[K] K, polynomialCoefficientLinear φ g ∈ I := by
  constructor
  · intro hg φ
    exact polynomialCoefficientLinear_mem_scalar_extension I g hg φ
  · intro h
    obtain ⟨s, hs⟩ := polynomial_coefficient_basis_expansion (Module.Free.chooseBasis K L) g
    rw [hs]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

end
end CCDN
