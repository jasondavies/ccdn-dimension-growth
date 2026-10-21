/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.BoundedDegreeFunctionFieldRank
public import CCDN.Hilbert.HilbertLinearCoordinates
public import CCDN.Projection.ProjectionFractionField
public import CCDN.Curve.CurvePrimitivePair
/-! Bounded primitive augmentation of any independent linear parameter
tuple of the Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_bounded_linear_parameter_primitive
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ k : ℕ, k ≤ n * d ^ 2 ∧
      IntermediateField.adjoin K
        (Set.range (fun i : Fin (m + 2) =>
          algebraMap (MvPolynomial (Fin n) K ⧸ I) F
            ((Ideal.Quotient.mk I) (Fin.cases (momentCoordinate K n k) l i)))) = ⊤ := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let A := MvPolynomial (Fin n) K ⧸ I
  let φ := IsScalarTower.toAlgHom K A F
  let u : Fin (m + 1) → F := fun i => φ ((Ideal.Quotient.mk I) (l i))
  let R := IntermediateField.adjoin K (Set.range u)
  let uR : Fin (m + 1) → R := fun i =>
    ⟨u i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hiA : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (l i)) := by
    change Function.Injective (aeval (fun i => (Ideal.Quotient.mk I) (l i)))
    rw [← projectionCoordinateMap_eq_aeval]
    exact hi
  have hiF : AlgebraicIndependent K u := hiA.map' (IsFractionRing.injective A F)
  have hiR : AlgebraicIndependent K uR := AlgebraicIndependent.of_comp R.val hiF
  obtain ⟨hfinite, hrank⟩ := hilbert_functionField_finite_rank_le (R := R) (F := F) I d
    (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hdegree) l hl uR hiR (fun _ => rfl)
  let : Module.Finite R F := hfinite
  obtain ⟨k, hk, hprim⟩ := exists_bounded_curve_primitive_element (R := R) (F := F) I
  refine ⟨k, hk.trans (Nat.mul_le_mul_left n (Nat.pow_le_pow_left hrank 2)), ?_⟩
  have hprim' : IntermediateField.adjoin R
      {φ ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤ := by
    change IntermediateField.adjoin R
      {algebraMap A F ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤
    rwa [momentCoordinate_fraction]
  have hh := primitive_parameter_tuple_adjoin_top u
    (φ ((Ideal.Quotient.mk I) (momentCoordinate K n k))) hprim'
  convert hh using 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end
end CCDN
