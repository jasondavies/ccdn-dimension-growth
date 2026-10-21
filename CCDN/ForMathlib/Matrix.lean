/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of dependent block-diagonal matrices

Mathlib computes `Matrix.det_blockDiagonal` for blocks of a common size. This file treats
`Matrix.blockDiagonal'`, whose blocks may have different sizes.

## Main results

* `Matrix.det_blockDiagonal'`: the determinant of `blockDiagonal' M` is the product of the
  determinants of the blocks.
-/

@[expose] public section

namespace Matrix

variable {o R : Type*} {m' : o → Type*} [Fintype o] [DecidableEq o]
  [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommRing R]

/-- The determinant of a block-diagonal matrix with blocks of varying sizes is the product of
the determinants of its blocks. -/
theorem det_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder o := LinearOrder.lift' (Fintype.equivFin o) (Fintype.equivFin o).injective
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e := (Equiv.sigmaSubtype (β := m') i).symm
  have he : ((blockDiagonal' M).toSquareBlock Sigma.fst i).submatrix e e = M i := by
    ext j k
    exact blockDiagonal'_apply_eq M i j k
  rw [← he, det_submatrix_equiv_self]

end Matrix
