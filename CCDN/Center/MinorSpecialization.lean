/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.MinorCoordinateDegree
public import CCDN.Height.ProjectiveZeroLocus
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! The sharp numerical specialization in CCDN Lemma 5.3. A
nonvanishing homogeneous condition on Plücker coordinates has a full-rank
integer witness with entries at most max(1, deg F), without a factor from
the number of rows. Every maximal minor has the stated factorial height
bound. The construction of the geometric bad-center polynomial is separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem homogeneous_minor_nonvanishing_implies_independent
    {r n : ℕ} (F : MvPolynomial (Fin r ↪ Fin n) ℚ)
    (hhom : F.IsHomogeneous F.totalDegree) (hdeg : 0 < F.totalDegree)
    (A : Matrix (Fin r) (Fin n) ℚ)
    (hF : eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) F ≠ 0) :
    LinearIndependent ℚ A.row := by
  classical
  by_contra hli
  have hz (c : Fin r ↪ Fin n) : (A.submatrix id c).det = 0 := by
    by_contra hd
    apply hli
    apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ c)
    exact Matrix.linearIndependent_rows_of_det_ne_zero hd
  apply hF
  have he : (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) = fun _ => 0 := funext hz
  rw [he]
  change eval (0 : (Fin r ↪ Fin n) → ℚ) F = 0
  simpa only [zero_smul, zero_pow hdeg.ne', zero_mul] using
    homogeneous_eval_smul hhom (0 : ℚ) (fun _ => 0)

end
end CCDN
