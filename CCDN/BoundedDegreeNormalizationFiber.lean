module

public import CCDN.IntegralFiberRank
public import CCDN.BoundedDegreeFunctionFieldRank
public import CCDN.HilbertLinearCoordinates
public import CCDN.ProjectionFractionField

/-! Sharp fibers of integral polynomial parameters of degree at most q.
The actual Hilbert multiplicity bounds the field degree by d*q^dimension;
a separating integral element gives the same bound for every finite fiber. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem bounded_degree_normalization_fiber_card_le_of_fractionField
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) E]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) E]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) E]
    (q : ℕ) (hq : 0 < q)
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ q)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (z : Fin (m + 1) → K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ d * q ^ (m + 1) := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let η : A →ₐ[K] E := IsScalarTower.toAlgHom K A E
  let v : Fin (m + 1) → E := fun i => η ((Ideal.Quotient.mk I) (l i))
  let R := IntermediateField.adjoin K (Set.range v)
  let u : Fin (m + 1) → R := fun i =>
    ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hiA : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (l i)) := by
    change Function.Injective (aeval (fun i => (Ideal.Quotient.mk I) (l i)))
    rw [← projectionCoordinateMap_eq_aeval]
    exact hi
  have hiE : AlgebraicIndependent K v := hiA.map' (IsFractionRing.injective A E)
  have hiR : AlgebraicIndependent K u :=
    AlgebraicIndependent.of_comp (x := u) R.val hiE
  obtain ⟨hfinite, hrank⟩ := bounded_degree_hilbert_functionField_finite_rank_le (R := R) (F := E) I d q hq
    (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hdegree) l hl u hiR (fun _ => rfl)
  let : Module.Finite R E := hfinite
  let P := MvPolynomial (Fin (m + 1)) K
  let ψ : P →ₐ[K] A := projectionCoordinateMap I l
  let ρ : P →ₐ[K] R := aeval u
  have hcomp : R.val.comp ρ = η.comp ψ := by
    ext i
    simp only [AlgHom.comp_apply, ρ, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let : Algebra P A := ψ.toRingHom.toAlgebra
  let : Algebra P R := ρ.toRingHom.toAlgebra
  let : Algebra P E := (η.comp ψ).toRingHom.toAlgebra
  let : IsScalarTower P A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower P R E := IsScalarTower.of_algebraMap_eq
    (fun p => congrArg (fun f : P →ₐ[K] E => f p) hcomp.symm)
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
  have hbound := integral_projection_fiber_card_le_finrank I l rfl R E hint z s hzero hproj
  simpa only [Fintype.card_fin] using
    hbound.trans hrank

/-- The fiber bound for the given normalization, with the function field
and all degree estimates supplied by the actual coordinate ring. -/
theorem bounded_degree_normalization_fiber_card_le
    {K : Type*} [Field K] [CharZero K] {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (q : ℕ) (hq : 0 < q)
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ q)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (z : Fin (m + 1) → K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ d * q ^ (m + 1) :=
  bounded_degree_normalization_fiber_card_le_of_fractionField
    (E := FractionRing (MvPolynomial (Fin n) K ⧸ I)) I q hq l hl hi hint d hdim hdegree z s hzero hproj

end
end CCDN
