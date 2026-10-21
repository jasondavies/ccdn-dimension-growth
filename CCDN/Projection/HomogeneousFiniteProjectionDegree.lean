/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.LinearProjectionFiltration
import CCDN.Projection.FiniteBirationalConductor
import CCDN.Projection.HomogeneousBirationalDegree
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Projection.ProjectionFractionField
/-! A homogeneous finite birational linear projection preserves the
Hilbert multiplicity. Both the conductor and the dimension equality
are consequences of the algebraic hypotheses. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem homogeneous_finite_birational_projection_leadingCoeff_eq
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    [Algebra (MvPolynomial τ K ⧸ I) F]
    [IsScalarTower K (MvPolynomial τ K ⧸ I) F]
    [IsFractionRing (MvPolynomial τ K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (hfield : IntermediateField.adjoin K
      (Set.range (fun i => algebraMap (MvPolynomial τ K ⧸ I) F
        ((Ideal.Quotient.mk I) (a i)))) = ⊤) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
      (filteredHilbertPolynomial I).leadingCoeff := by
  let A := MvPolynomial τ K ⧸ I
  let ψ := projectionCoordinateMap I a
  let J := RingHom.ker ψ
  have : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let R := MvPolynomial σ K ⧸ J
  let φ : R →ₐ[K] A := Ideal.kerLiftAlg ψ
  let η : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let : Algebra R A := φ.toRingHom.toAlgebra
  let : IsScalarTower K R A := IsScalarTower.of_algHom φ
  let : Algebra R F := (η.comp φ).toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (η.comp φ) :=
    (IsFractionRing.injective A F).comp (Ideal.kerLiftAlg_injective ψ)
  let : IsFractionRing R F := isFractionRing_of_generating_tuple
    (η.comp φ) hinj (fun i => (Ideal.Quotient.mk J) (X i)) (by
      convert hfield using 2
      congr 1
      funext i
      change algebraMap A F ((Ideal.Quotient.mk I) (aeval a (X i))) =
        algebraMap A F ((Ideal.Quotient.mk I) (a i))
      rw [aeval_X])
  let : Algebra.IsIntegral R A := ⟨hint.kerLift⟩
  let : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let : Module.Finite R A := Algebra.IsIntegral.finite
  obtain ⟨c, hc, hconductor⟩ := exists_nonzero_finite_birational_conductor R A F
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective c
  let q := aeval a p
  have hq : (Ideal.Quotient.mk I) q = φ c := by
    rw [← hp]
    rfl
  have hqne : (Ideal.Quotient.mk I) q ≠ 0 := by
    rw [hq]
    exact (map_ne_zero_iff φ (Ideal.kerLiftAlg_injective ψ)).mpr hc
  apply homogeneous_projection_leadingCoeff_eq I hI a ha
    (integral_projection_hilbert_dimension_eq I ψ hint) q hqne
  intro x
  obtain ⟨r, hr⟩ := hconductor x
  obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨p', ?_⟩
  rw [hq]
  change φ ((Ideal.Quotient.mk J) p') = φ c * x
  rw [hp']
  exact hr

end
end CCDN
