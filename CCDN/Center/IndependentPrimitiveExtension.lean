/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ProjectionImageFractionField
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial
import CCDN.Center.IndependentProjectionRows
import CCDN.Height.LinearParameterPrimitive
import CCDN.Hilbert.HilbertLinearCoordinates
import CCDN.Projection.BoundedInfinityAvoidance
import Mathlib.RingTheory.AlgebraicIndependent.Basic
/-! An independent homogeneous normalization can be augmented by
one homogeneous linear form to a finite birational tuple, while retaining
every original normalization coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_variable_outside_independent_span
    {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K) (ha : LinearIndependent K a)
    (hmn : m < n) :
    ∃ j : Fin n, X j ∉ Submodule.span K (Set.range a) := by
  classical
  by_contra! h
  have hle : Submodule.span K (Set.range (X : Fin n → MvPolynomial (Fin n) K)) ≤
      Submodule.span K (Set.range a) :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  let : Module.Finite K (Submodule.span K (Set.range a)) :=
    Module.Finite.span_of_finite K (Set.finite_range a)
  have hh := Submodule.finrank_mono hle
  rw [finrank_span_eq_card (linearIndependent_X (Fin n) K), finrank_span_eq_card ha,
    Fintype.card_fin, Fintype.card_fin] at hh
  omega

theorem exists_independent_linear_primitive_extension
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (a : Fin (m + 1) → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (hinj : Function.Injective (projectionCoordinateMap I a))
    (hmn : m + 2 ≤ n) (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ v : MvPolynomial (Fin n) K,
      v.IsHomogeneous 1 ∧ LinearIndependent K (Fin.cons v a) ∧
      (projectionCoordinateMap I (Fin.cons v a)).IsIntegral ∧
      projectionImageField (F := F) I (Fin.cons v a) = ⊤ := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let T : MvPolynomial (Fin n) K →ₗ[K] F :=
    (IsScalarTower.toAlgHom K A F).toLinearMap.comp (Ideal.Quotient.mkₐ K I).toLinearMap
  have hai : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i)) :=
    injective_projectionCoordinateMap_iff.mp hinj
  have hali : LinearIndependent K a :=
    hai.linearIndependent.of_comp (Ideal.Quotient.mkₐ K I).toLinearMap
  obtain ⟨k, _, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I a (fun i => (ha i).totalDegree_le) hinj d hdimdeg
  let p := momentCoordinate K n k
  have hfieldp : projectionImageField (F := F) I (Fin.cons p a) = ⊤ := hfield
  suffices ∃ v : MvPolynomial (Fin n) K,
      v.IsHomogeneous 1 ∧ LinearIndependent K (Fin.cons v a) ∧
      projectionImageField (F := F) I (Fin.cons v a) = ⊤ by
    obtain ⟨v, hv, hvi, hvg⟩ := this
    refine ⟨v, hv, hvi, ?_, hvg⟩
    have he : (projectionCoordinateMap I (Fin.cons v a)).comp (rename Fin.succ) =
        projectionCoordinateMap I a := by
      ext i
      simp [projectionCoordinateMap]
    apply RingHom.IsIntegral.tower_top (rename Fin.succ).toRingHom
      (projectionCoordinateMap I (Fin.cons v a)).toRingHom
    change ((projectionCoordinateMap I (Fin.cons v a)).comp (rename Fin.succ)).IsIntegral
    rwa [he]
  by_cases hi : LinearIndependent K (Fin.cons p a)
  · exact ⟨p, momentCoordinate_homogeneous K n k, hi, hfieldp⟩
  have hdep : p ∈ Submodule.span K (Set.range a) := by
    by_contra hn
    exact hi (hali.finCons hn)
  have htail : projectionImageField (F := F) I a = ⊤ := by
    have hh := adjoin_linear_images_eq_tail_of_first_mem_span (Fin.cons p a) T hdep
    simpa only [Fin.cons_zero, Fin.cons_succ, projectionImageField, T,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      IsScalarTower.toAlgHom_apply] using hh.symm.trans hfieldp
  obtain ⟨j, hj⟩ := exists_variable_outside_independent_span a hali (by omega)
  refine ⟨X j, isHomogeneous_X K j, hali.finCons hj, ?_⟩
  apply top_unique
  rw [← htail]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact IntermediateField.subset_adjoin K _ (Set.mem_range_self i.succ)

end
end CCDN
