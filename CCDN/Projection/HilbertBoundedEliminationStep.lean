module

public import CCDN.Hilbert.HilbertLowDegreeEquation
public import CCDN.Projection.BoundedLinearElimination
public import CCDN.Projection.IntegralProjectionHilbert
/-! A complete bounded elimination step: the contraction stays prime,
retains dimension, and has no larger Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def eliminationLinearCoordinates {σ : Type*} (b : Option σ → ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  fun i => X (some i) - C (b (some i) / b none) * X none

lemma coordinateEliminationMap_eq_projection {σ : Type*}
    (I : Ideal (MvPolynomial (Option σ) ℚ)) (b : Option σ → ℚ) (hb : b none ≠ 0) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) =
      projectionCoordinateMap I (eliminationLinearCoordinates b) := by
  ext i
  rw [coordinateEliminationMap_direction_X]
  simp [projectionCoordinateMap, eliminationLinearCoordinates]

end
end CCDN
