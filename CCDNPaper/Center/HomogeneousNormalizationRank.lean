/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Hilbert.LinearCoordinates
import CCDN.Projection.LeadingCoordinateExtension
import CCDN.Projection.LinearParameterPrimitive
import CCDN.Projection.PrimitiveCoordinateField
import CCDNPaper.Center.HomogeneousIntegralRelation
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
The field degree of a homogeneous finite linear normalization
is exactly the Hilbert multiplicity. The proof constructs the equation, its
monicity up to a unit, and a primitive element.

Primitive augmentation of a finite homogeneous normalization
produces an irreducible equation whose degree in the new variable is exactly
the Hilbert multiplicity.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The equation is constructed from the given normalization; its homogeneous
and univariate degrees are both the Hilbert multiplicity. -/
private theorem exists_homogeneous_normalization_primitive_equation
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin (m + 1) → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hi : Function.Injective (projectionCoordinateMap I a))
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ z : MvPolynomial (Fin n) K, ∃ f : MvPolynomial (Fin (m + 2)) K,
      IntermediateField.adjoin K
        (Set.range (fun i : Fin (m + 2) => algebraMap (MvPolynomial (Fin n) K ⧸ I) F
          ((Ideal.Quotient.mk I) (Fin.cases z a i)))) = ⊤ ∧
      Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧ 0 < d ∧
      RingHom.ker (projectionCoordinateMap I (Fin.cases z a)) = Ideal.span {f} ∧
      (finSuccEquiv K (m + 1) f).natDegree = d := by
  classical
  obtain ⟨k, _, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I a (fun i => (ha i).totalDegree_le) hi d hdimdeg
  let z := momentCoordinate K n k
  let l : Fin (m + 2) → MvPolynomial (Fin n) K := Fin.cases z a
  have hl (i) : (l i).IsHomogeneous 1 := by
    refine Fin.cases ?_ (fun j => ha j) i
    change (momentCoordinate K n k).IsHomogeneous 1
    unfold momentCoordinate
    exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X ((k : K) ^ j.val) j)
  obtain ⟨f, hf, hfhom, hfdeg, hd, hker⟩ := exists_homogeneous_extended_projection_equation
    (F := F) I hI l hl hint hi hfield d hdimdeg
  exact ⟨z, f, hfield, hf, hfhom, hfdeg, hd, hker,
    integral_homogeneous_projection_relation_natDegree I a hint z f hfhom hker⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma parameter_primitive_adjoin_top_of_tuple
    {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}
    (u : Fin m → F) (v : F)
    (h : IntermediateField.adjoin K (Set.range (Fin.cases v u : Fin (m + 1) → F)) = ⊤) :
    IntermediateField.adjoin (IntermediateField.adjoin K (Set.range u)) {v} = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top]
  convert h using 2
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.succ, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact Or.inl ⟨j, rfl⟩

/-- Exact normalization rank over its parameter subfield, for any
chosen fraction field of the homogeneous prime coordinate ring. -/
theorem homogeneous_normalization_functionField_finrank
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin (m + 1) → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hi : Function.Injective (projectionCoordinateMap I a))
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    Module.finrank (IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (a i))))) F = d := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let η : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let v : Fin (m + 1) → F := fun i => η ((Ideal.Quotient.mk I) (a i))
  let R := IntermediateField.adjoin K (Set.range v)
  let u : Fin (m + 1) → R := fun i =>
    ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hiA : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i)) :=
    injective_projectionCoordinateMap_iff.mp hi
  have hiF : AlgebraicIndependent K v := hiA.map' (IsFractionRing.injective A F)
  have hiR : AlgebraicIndependent K u := AlgebraicIndependent.of_comp R.val hiF
  let P := MvPolynomial (Fin (m + 1)) K
  let ψ : P →ₐ[K] A := projectionCoordinateMap I a
  let ρ : P →ₐ[K] R := aeval u
  have hcomp : R.val.comp ρ = η.comp ψ := by
    ext i
    simp only [AlgHom.comp_apply, ρ, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let : Algebra P R := ρ.toRingHom.toAlgebra
  have hgen : IntermediateField.adjoin K (Set.range u) = ⊤ := by
    apply IntermediateField.lift_injective R
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
    rfl
  let : IsFractionRing P R := isFractionRing_of_generating_tuple ρ hiR
    (fun i => X i) (by
      convert hgen using 2
      congr 1
      funext i
      change (aeval u) (X i) = u i
      rw [aeval_X])
  obtain ⟨z, f, hfield, hf, _, _, hd, hker, hdeg⟩ :=
    exists_homogeneous_normalization_primitive_equation (F := F) I hI a ha hi hint d hdimdeg
  let w := η ((Ideal.Quotient.mk I) z)
  let p : Polynomial P := finSuccEquiv K (m + 1) f
  have hp : Irreducible p := (MulEquiv.irreducible_iff (finSuccEquiv K (m + 1))).mpr hf
  have hpprim : p.IsPrimitive :=
    hp.isPrimitive (by change (finSuccEquiv K (m + 1) f).natDegree ≠ 0; omega)
  let q : Polynomial R := p.map (algebraMap P R)
  have hq : Irreducible q := hpprim.irreducible_iff_irreducible_map_fraction_map.mp hp
  have hqdeg : q.natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective P R)]
    exact hdeg
  have heA : p.eval₂ ψ.toRingHom ((Ideal.Quotient.mk I) z) = 0 :=
    projection_relation_eval₂_eq_zero I a z f hker
  have he : Polynomial.aeval w q = 0 := by
    have hh := congrArg η heA
    change η.toRingHom (p.eval₂ ψ.toRingHom ((Ideal.Quotient.mk I) z)) = η.toRingHom 0 at hh
    rw [Polynomial.hom_eval₂, map_zero] at hh
    change p.eval₂ (η.toRingHom.comp ψ.toRingHom) w = 0 at hh
    change (p.map ρ.toRingHom).eval₂ R.val.toRingHom w = 0
    rw [Polynomial.eval₂_map]
    exact (congrArg (fun h : P →ₐ[K] F => p.eval₂ h.toRingHom w) hcomp).trans hh
  have hmin : (minpoly R w).natDegree = d := by
    rw [← minpoly.eq_of_irreducible hq he,
      Polynomial.natDegree_mul_C_of_isUnit (isUnit_iff_ne_zero.mpr
        (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq.ne_zero)))]
    exact hqdeg
  have hprim : IntermediateField.adjoin R {w} = ⊤ := by
    apply parameter_primitive_adjoin_top_of_tuple v w
    convert hfield using 2
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hw : IsIntegral R w := IsAlgebraic.isIntegral ⟨q, hq.ne_zero, he⟩
  change Module.finrank R F = d
  rw [← IntermediateField.finrank_top' (F := R) (E := F), ← hprim,
    IntermediateField.adjoin.finrank hw]
  exact hmin

end
end CCDN
