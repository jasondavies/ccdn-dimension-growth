/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.LinearProjectionFiltration
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CCDN.Projection.IntegralProjectionClosedImage

/-! The image of an integral polynomial projection over an
algebraically closed field is exactly the zero locus of its kernel.
This is the `Fin n`-indexed case of `integral_projection_exists_point`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Specialisation of `integral_projection_exists_point` to `Fin`-indexed
variables and coordinates. -/
theorem exists_point_of_integral_projection_kernel_zero
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : Fin m → K)
    (hz : ∀ f ∈ RingHom.ker (projectionCoordinateMap I a), eval z f = 0) :
    ∃ x : Fin n → K, (∀ f ∈ I, eval x f = 0) ∧
      ∀ i, eval x (a i) = z i :=
  integral_projection_exists_point I a hint z hz

end
end CCDN
