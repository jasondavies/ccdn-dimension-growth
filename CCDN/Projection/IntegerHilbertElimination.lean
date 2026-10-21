module

public import CCDN.Projection.HilbertBoundedEliminationStep
public import CCDN.Noether.GenericPlaneStretch
/-! Bounded integral linear elimination with integer coefficients.
Scaling the retained coordinates by the nonzero pivot preserves integrality. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def integerEliminationCoordinates {σ : Type*} (b : Option σ → ℤ) :
    σ → MvPolynomial (Option σ) ℚ :=
  fun i => C (b none : ℚ) * X (some i) - C (b (some i) : ℚ) * X none

lemma integerEliminationCoordinates_eq_scale {σ : Type*}
    (b : Option σ → ℤ) (hb : (b none : ℚ) ≠ 0) (i : σ) :
    integerEliminationCoordinates b i =
      C (b none : ℚ) * eliminationLinearCoordinates (fun i => (b i : ℚ)) i := by
  have hh : (b none : ℚ) * ((b (some i) : ℚ) / b none) = b (some i) := by
    field_simp
  dsimp only [integerEliminationCoordinates, eliminationLinearCoordinates]
  rw [mul_sub, ← mul_assoc, ← map_mul, hh]

theorem integerEliminationMap_isIntegral {σ : Type*}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) (b : Option σ → ℤ)
    (hb : (b none : ℚ) ≠ 0)
    (hint : (projectionCoordinateMap I
      (eliminationLinearCoordinates (fun i => (b i : ℚ)))).IsIntegral) :
    (projectionCoordinateMap I (integerEliminationCoordinates b)).IsIntegral := by
  let e := variableScaleEquiv ℚ σ (b none : ℚ) hb
  let ψ := projectionCoordinateMap I (eliminationLinearCoordinates (fun i => (b i : ℚ)))
  have he : e.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ e.surjective
  have hcomp := RingHom.IsIntegral.trans e.toRingHom ψ.toRingHom he hint
  have heq : ψ.comp e.toAlgHom = projectionCoordinateMap I (integerEliminationCoordinates b) := by
    ext i
    change ψ (e (X i)) =
      projectionCoordinateMap I (integerEliminationCoordinates b) (X i)
    rw [show e (X i) = C (b none : ℚ) * X i from variableScaleEquiv_X _ hb i]
    change (Ideal.Quotient.mkₐ ℚ I) (aeval
      (eliminationLinearCoordinates (fun i => (b i : ℚ))) (C (b none : ℚ) * X i)) =
        (Ideal.Quotient.mkₐ ℚ I) (aeval (integerEliminationCoordinates b) (X i))
    rw [map_mul, aeval_C, aeval_X, aeval_X, integerEliminationCoordinates_eq_scale b hb,
      algebraMap_eq]
  change (ψ.comp e.toAlgHom).IsIntegral at hcomp
  rwa [heq] at hcomp

end
end CCDN
