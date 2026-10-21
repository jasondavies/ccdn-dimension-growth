/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.PlaneSmoothGeometricIrreducibility
public import CCDN.ForMathlib.MatrixRank
import CCDN.Noether.ClosedFormRank
import CCDN.Noether.ShearNormalization

/-! A smooth rational point supplies a nonzero closed-form coefficient minor
for an irreducible plane equation in characteristic zero or large characteristic.
The base field need not be algebraically closed. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- A nonzero minor over the original coefficient field, obtained by proving
geometric irreducibility from the smooth point. -/
theorem exists_closedForm_minor_of_smooth_plane_point
    {K : Type*} [Field K]
    (d : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2)) :
    (closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp only [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm : g.Monic := bivariateMap_monic φ hm
  have hgd : g.degree = d := by
    rw [degree_eq_natDegree hgm.ne_zero, bivariateMap_natDegree_of_monic φ hm, hdeg]
  have hgt : bivariateTotalDegree g ≤ d := by
    apply (bivariateTotalDegree_map_le φ _).trans
    simpa only [bivariateTotalDegree, AlgEquiv.symm_apply_apply] using htotal
  have hr := closedForm_coefficient_rank_lower d g hgi hgm hgd d hgt
    ((hchar.map φ).mono (by rw [sq, mul_assoc]))
  obtain ⟨a, c, hdet⟩ := Matrix.hasNonzeroMinor_of_le_rank
    (closedFormCoefficientMatrix d g) (r := 2 * d ^ 2 - 1) (by omega)
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [← closedForm_minor_map, he, map_zero]

end
end CCDN
