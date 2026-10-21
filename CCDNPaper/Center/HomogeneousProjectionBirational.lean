/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ImageFractionField
import CCDN.Projection.HomogeneousFiniteProjectionDegree
import CCDNPaper.Center.HomogeneousProjectionRankBound
import CCDNPaper.Hypersurface.SmallOutsidePoint
import CCDNPaper.Hypersurface.ZeroDimensionalPrimeDescent

/-!
A finite homogeneous linear projection preserves the Hilbert
multiplicity if and only if its projected coordinates generate the source
function field. This includes the zero-dimensional affine cone.

A homogeneous prime ideal of Hilbert dimension zero is the origin.
Its function field therefore has no extension beyond the coefficient field.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem homogeneous_zero_dimension_projectionImageField_eq_top
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

namespace CCDN
noncomputable section
open MvPolynomial

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}
  (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
  [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
  [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
  [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]

/-- Equality of source and image multiplicities forces birationality.
The proof constructs the image field, a finite linear normalization, and its
rank. -/
theorem homogeneous_finite_projection_birational_of_leadingCoeff_eq {s : ℕ}
    (hI : IsHomogeneousIdeal I)
    (a : Fin s → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (heq : (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff) :
    projectionImageField (F := F) I a = ⊤ := by
  by_cases hzero : (filteredHilbertPolynomial I).natDegree = 0
  · exact homogeneous_zero_dimension_projectionImageField_eq_top I hI hzero a
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  obtain ⟨d, hd, hdimdeg⟩ := exists_hasAffineDimensionDegree I (Ideal.IsPrime.ne_top ‹I.IsPrime›) hm
  obtain ⟨hfinite, hrank⟩ := homogeneous_projection_functionField_rank_bound (F := F)
    I hI a ha hint d d hdimdeg (heq.trans hdimdeg.leadingCoeff_eq)
  let L := projectionImageField (F := F) I a
  let : Module.Finite L F := hfinite
  have hpos : 0 < Module.finrank L F := Module.finrank_pos
  apply IntermediateField.finrank_eq_one_iff_eq_top.mp
  change Module.finrank L F = 1
  nlinarith

/-- Degree preservation and function-field birationality are equivalent for
a finite homogeneous linear projection in characteristic zero. -/
theorem homogeneous_finite_projection_leadingCoeff_eq_iff_birational {s : ℕ}
    (hI : IsHomogeneousIdeal I)
    (a : Fin s → MvPolynomial (Fin n) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff ↔
    projectionImageField (F := F) I a = ⊤ := by
  constructor
  · exact homogeneous_finite_projection_birational_of_leadingCoeff_eq I hI a ha hint
  · exact homogeneous_finite_birational_projection_leadingCoeff_eq I hI a ha hint

end
end CCDN
