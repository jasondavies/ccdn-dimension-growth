/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.AmbientNoetherForms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.UniversalPlaneEulerMinorCharZero
import CCDN.Noether.AmbientNoetherVanishing
/-! Characteristic-zero nonvanishing of the ambient integer
coefficient forms, descended from the algebraic closure. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Some constructed universal form detects every absolutely irreducible
homogeneous equation in characteristic zero. -/
theorem exists_ambientNoetherForm_nonzero {K σ : Type*}
    [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
      (m : PlaneParameters (Option σ) →₀ ℕ),
      homogeneousCoefficientSpecialization (k + 2) f
        (ambientNoetherForm (Option σ) k rows cols m) ≠ 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hd : (MvPolynomial.map φ f).totalDegree = k + 2 := (hf.map φ).totalDegree hir.ne_zero
  obtain ⟨rows, cols, hdet⟩ := exists_universalPlane_euler_minor_charZero
    k (MvPolynomial.map φ f) hir hd
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hdet
  refine ⟨rows, cols, m, ?_⟩
  intro hz
  apply hm
  rw [← ambientEuler_minor_map φ k f rows cols, coeff_map,
    ← ambientNoetherForm_specialize k f hf rows cols m, hz, map_zero]

end
end CCDN
