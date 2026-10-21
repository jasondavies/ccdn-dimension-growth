module

public import CCDN.Height.IntegralAlgebraPointCount
public import CCDN.Projection.LinearProjectionFiltration
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Rational-point fibers of an integral polynomial projection.
Evaluation on the quotient constructs the specialization homomorphisms,
and normality of the polynomial base gives a uniform fiber bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A rational point of the fiber over `z` gives a specialization of the quotient algebra over
the parameter ring, sending each coordinate function to the corresponding coordinate. -/
theorem exists_projection_fiber_specialization {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (z : τ → K) (x : σ → K) (hzero : ∀ f ∈ I, eval x f = 0)
    (hproj : ∀ i, eval x (l i) = z i) :
    letI : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
    ∃ ψ : (MvPolynomial σ K ⧸ I) →ₐ[MvPolynomial τ K] K,
      ∀ i, ψ (Ideal.Quotient.mk I (X i)) = x i := by
  let : Algebra (MvPolynomial τ K) K := (aeval z).toRingHom.toAlgebra
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ : A →ₐ[K] K := Ideal.Quotient.liftₐ I (aeval x) (fun f hf => hzero f hf)
  have hφ (f : MvPolynomial σ K) :
      φ (Ideal.Quotient.mk I f) = eval x f := by
    exact congrArg (fun g : MvPolynomial σ K →ₐ[K] K => g f)
      (Ideal.Quotient.liftₐ_comp I (aeval x) (fun f hf => hzero f hf))
  have hcomp : φ.comp (projectionCoordinateMap I l) = aeval z := by
    ext i
    simpa only [projectionCoordinateMap, AlgHom.comp_apply, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk] using (hφ (l i)).trans (hproj i)
  let ψ : A →ₐ[R] K :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap R A r) = (aeval z) r
        rw [hmap]
        exact congrArg (fun f : R →ₐ[K] K => f r) hcomp }
  refine ⟨ψ, ?_⟩
  intro i
  change φ (Ideal.Quotient.mk I (X i)) = x i
  simpa only [eval_X] using hφ (X i)

theorem integral_projection_fiber_card_le
    {K σ τ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (F E : Type*) [Field F] [Field E]
    [Algebra (MvPolynomial τ K) F] [IsFractionRing (MvPolynomial τ K) F]
    [Algebra (MvPolynomial τ K) E] [Algebra (MvPolynomial σ K ⧸ I) E]
    [Algebra F E]
    [IsScalarTower (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) E]
    [IsScalarTower (MvPolynomial τ K) F E] [FiniteDimensional F E]
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (z : τ → K) (s : Finset (σ → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ (Module.finrank F E) ^ Fintype.card σ := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let b : σ → A := fun i => Ideal.Quotient.mk I (X i)
  let : Algebra R K := (aeval z).toRingHom.toAlgebra
  have hb (i) : IsIntegral R (b i) := by
    change (algebraMap R A).IsIntegralElem (b i)
    rw [hmap]
    exact hint (b i)
  apply integral_coordinate_tuple_count_le_finrank_pow R A F E b hb s
  intro x hx
  exact exists_projection_fiber_specialization I l hmap z x (hzero x hx) (hproj x hx)

end
end CCDN
