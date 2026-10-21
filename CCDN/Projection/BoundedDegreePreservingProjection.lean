/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Curve.CurvePrimitivePair
public import CCDN.Projection.InfinityParameterReduction
import CCDN.Curve.CurveRationalParameter
import CCDN.Hilbert.RecurrenceParameterTranscendence
import CCDN.Projection.BoundedInfinityAvoidance
import CCDN.Projection.BoundedInfinityParameter
import CCDN.Projection.DegreePreservingProjectionCount
import CCDN.Projection.FullDegreePrimitiveProjection
/-! Every positive-degree prime affine curve in characteristic zero admits
an explicitly bounded integral linear plane projection preserving its degree.
The first coordinate is constructed by infinity avoidance and the second by
the quantitative primitive-element theorem. -/

@[expose] public section
namespace CCDN
noncomputable section

section

/-! An infinity-avoiding linear form gives a degree-preserving plane
projection. The parameter field and the second coordinate are constructed. -/

open MvPolynomial

/-- Avoiding infinity and the certified affine Hilbert degree suffice for a
degree-preserving plane projection. -/
theorem exists_degree_preserving_projection_of_infinity_avoidance {K L F : Type*}
    [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ m ≥ M,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (l : MvPolynomial (Fin n) K) (hl : l.IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I ⊔ Ideal.span {l}), z = 0) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      Irreducible f ∧ f.totalDegree = d ∧
      ∀ g, aeval (![l, momentCoordinate K n k]) g ∈ I ↔ f ∣ g := by
  obtain ⟨N, hrec⟩ := filtration_recurrence_of_infinity_avoidance I l hl hzero
  have hu := recurrence_parameter_transcendental I d hd hdegree l N hrec
  let u := algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l)
  have huF : Transcendental K u := by
    intro h
    exact hu ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F)
      (IsFractionRing.injective _ _)).mp h)
  let φ := transcendentalRatFuncMap u huF
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algHom φ
  apply exists_full_degree_primitive_projection (F := F) I d hdegree l hl.totalDegree_le
    _ N hrec
  exact (transcendentalRatFuncMap_X u huF).symm

end

open MvPolynomial

/-- A bounded degree-preserving plane projection of a prime affine curve in
characteristic zero. The curve need not be geometrically integral. -/
theorem exists_bounded_degree_preserving_projection {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      Transcendental K ((Ideal.Quotient.mk I) (momentCoordinate K n k₀)) ∧
      ∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g := by
  obtain ⟨k₀, hk₀, havoid⟩ := exists_bounded_infinity_parameter (L := AlgebraicClosure K) I d hdegree
  obtain ⟨N, hrec⟩ := filtration_recurrence_of_infinity_avoidance I
    (momentCoordinate K n k₀) (momentCoordinate_homogeneous K n k₀) havoid
  have htrans := recurrence_parameter_transcendental I d hd hdegree _ N hrec
  obtain ⟨k₁, f, hk₁, hf, hfd, hker⟩ :=
    exists_degree_preserving_projection_of_infinity_avoidance
      (F := FractionRing (MvPolynomial (Fin n) K ⧸ I)) I d hd hdegree
      (momentCoordinate K n k₀) (momentCoordinate_homogeneous K n k₀) havoid
  exact ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, htrans, hker⟩

/-- An integral affine curve of degree `d` has a projection to the plane by two moment
coordinates of bounded index whose image is cut out by an irreducible equation of degree `d`,
and which identifies at most `d(d-1)` points of any finite subset of the curve. -/
theorem exists_bounded_projection_card_le {K : Type*} [Field K] [CharZero K]
    [DecidableEq (Fin 2 → K)] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      (∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g) ∧
      ∀ S : Finset (Fin n → K), (∀ z ∈ S, z ∈ idealZeroLocus I) →
        S.card ≤ (S.image (fun z =>
          ![eval z (momentCoordinate K n k₀), eval z (momentCoordinate K n k₁)])).card +
            d * (d - 1) := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hu, hker⟩ :=
    exists_bounded_degree_preserving_projection I d hd hdegree
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, ?_⟩
  intro S hS
  let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
  have ha (j : Fin 2) : (a j).totalDegree ≤ 1 := by
    fin_cases j <;> exact momentCoordinate_degree _ _ _
  have hc := degree_preserving_projection_card_le I a ha d hdegree hu f hf.ne_zero hfd hker S hS
  convert hc using 1
  congr 3
  funext z j
  fin_cases j <;> rfl

end
end CCDN
