/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Homogeneous components and dimensions of homogeneous submodules

## Main results

* `MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_left`: multiplication by a
  homogeneous polynomial of degree `d` shifts homogeneous components by `d`.
* `MvPolynomial.finrank_homogeneousSubmodule`: over a field, the homogeneous polynomials of
  degree `n` in finitely many variables `σ` form a space of dimension
  `(Fintype.card σ + n - 1).choose n`.
* `MvPolynomial.finrank_homogeneousSubmodule_fin`: the same count for `n + 1` variables, in the
  form `(n + M).choose M`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*}

/-- Multiplication by a homogeneous polynomial of degree `d` shifts homogeneous components
by `d`. -/
theorem homogeneousComponent_mul_of_isHomogeneous_left [CommRing K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (u : MvPolynomial σ K) (k : ℕ) :
    homogeneousComponent (d + k) (f * u) = f * homogeneousComponent k u := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have ht := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule σ K) (j := k) hf (b := u)
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using ht

/-- The homogeneous polynomials of degree `n` in finitely many variables `σ` form a space of
dimension `(Fintype.card σ + n - 1).choose n`, the number of monomials of degree `n`. -/
theorem finrank_homogeneousSubmodule [Field K] [Fintype σ] (n : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K n) = (Fintype.card σ + n - 1).choose n := by
  classical
  let e : {p : σ →₀ ℕ // p.degree = n} ≃ Sym σ n :=
    ((Sym.equivNatSum σ n).trans
      (Equiv.subtypeEquivRight fun p => by simp [Finsupp.degree_apply, Finsupp.sum])).symm
  have he : homogeneousSubmodule σ K n = restrictSupport K {p | p.degree = n} := by
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  rw [he, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {p : σ →₀ ℕ // p.degree = n} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]

/-- The homogeneous polynomials of degree `M` in `n + 1` variables form a space of dimension
`(n + M).choose M`. -/
theorem finrank_homogeneousSubmodule_fin [Field K] (n M : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K M) = (n + M).choose M := by
  rw [finrank_homogeneousSubmodule, Fintype.card_fin]
  congr 1
  omega

end MvPolynomial
