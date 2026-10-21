/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Center.HomogeneousIntegralRelation
import CCDN.Projection.LinearParameterPrimitive
import CCDN.Projection.LeadingCoordinateExtension
/-! Primitive augmentation of a finite homogeneous normalization
produces an irreducible equation whose degree in the new variable is exactly
the Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The equation is constructed from the given normalization; its homogeneous
and univariate degrees are both the Hilbert multiplicity. -/
theorem exists_homogeneous_normalization_primitive_equation
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
