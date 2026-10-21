/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectionImageFractionField
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hypersurface.SmallOutsidePoint
import CCDN.Hypersurface.ZeroDimensionalPrimeDescent
/-! A homogeneous prime ideal of Hilbert dimension zero is the origin.
Its function field therefore has no extension beyond the coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem homogeneous_zero_dimension_projectionImageField_eq_top
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {σ : Type*}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (a : σ → MvPolynomial (Fin n) K) :
    projectionImageField (F := F) I a = ⊤ := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let L := projectionImageField (F := F) I a
  have hker := zero_dimensional_prime_eq_eval_kernel I hdim 0
    (homogeneous_ideal_eval_zero I (Ideal.IsPrime.ne_top ‹I.IsPrime›) hI)
  have hmem (x : A) : algebraMap A F x ∈ L := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : (Ideal.Quotient.mk I) p = algebraMap K A (eval 0 p) := by
      change (Ideal.Quotient.mk I) p = (Ideal.Quotient.mk I) (C (eval 0 p))
      apply Ideal.Quotient.eq.mpr
      rw [hker, RingHom.mem_ker, map_sub, eval_C, sub_self]
    rw [hp, ← IsScalarTower.algebraMap_apply K A F]
    exact L.algebraMap_mem _
  apply top_unique
  intro x _
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective A x
  exact L.div_mem (hmem p) (hmem q)

end
end CCDN
