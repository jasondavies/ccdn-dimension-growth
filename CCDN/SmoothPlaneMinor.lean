module

public import CCDN.PlaneSmoothGeometricIrreducibility
public import CCDN.PositiveCharacteristicRank
public import CCDN.ClosedFormIntegerMinor
public import CCDN.ShearNormalization
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! A smooth rational point supplies a nonzero closed-form coefficient minor
for an irreducible plane equation in large characteristic. The base field need
not be algebraically closed. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- A nonzero minor over the original coefficient field, obtained by proving
geometric irreducibility from the smooth point. -/
theorem exists_closedForm_minor_of_smooth_plane_point
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : 2 * d ^ 2 < p) :
    ∃ (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective a ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).submatrix a c).det ≠ 0 := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
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
  have hr := closedForm_coefficient_rank_lower_of_char (ell := p) d hd g hgi hgm hgd hgt hchar
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_nonzero_minor_of_rank_le
    (closedFormCoefficientMatrix d g) (2 * d ^ 2 - 1) (by omega)
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [← closedForm_minor_map, he, map_zero]

end
end CCDN
