/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormScaling
public import CCDN.Noether.UniversalPlaneWitnessCharZero
public import CCDN.Noether.UniversalPlaneEvaluation
public import CCDN.Algebra.IntegerPolynomialAvoidance
/-! A nonzero universal witness certifies a geometrically irreducible
 plane section in characteristic zero. Integer specialization can simultaneously
 avoid any additional nonzero polynomial condition on the plane parameters. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Nonvanishing certifies full degree and irreducibility over any target
field of characteristic zero, including its algebraic closure. -/
theorem universalPlaneBadWitness_good_specialization_charZero
    {K L σ : Type*} [CommRing K] [Field L] [CharZero L]
    (f : MvPolynomial σ K) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (φ : MvPolynomial (PlaneParameters σ) K →+* L)
    (hw : φ (universalPlaneBadWitness f rows cols) ≠ 0) :
    (bivariateMap φ (universalPlanePolynomial f)).natDegree = f.totalDegree ∧
      bivariateTotalDegree (bivariateMap φ (universalPlanePolynomial f)) = f.totalDegree ∧
      Irreducible (bivariateMap φ (universalPlanePolynomial f)) := by
  let g := bivariateMap φ (universalPlanePolynomial f)
  have hh := mul_ne_zero_iff.mp (show φ (universalPlaneLeading f) *
      φ (((closedFormCoefficientMatrix f.totalDegree (universalPlanePolynomial f)).submatrix rows cols).det) ≠ 0
      by simpa only [universalPlaneBadWitness, map_mul] using hw)
  have ht : bivariateTotalDegree g ≤ f.totalDegree :=
    universalPlanePolynomial_specialization_totalDegree f φ
  have hc : ((g.coeff f.totalDegree).coeff 0) ≠ 0 := by
    simpa only [g, bivariateMap_coeff, universalPlaneLeading] using hh.1
  have hd : g.natDegree = f.totalDegree := by
    apply le_antisymm ((bivariate_natDegree_le_totalDegree g).trans ht)
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    exact hc (by rw [hz, Polynomial.coeff_zero])
  have he : bivariateTotalDegree g = f.totalDegree :=
    le_antisymm ht (hd ▸ bivariate_natDegree_le_totalDegree g)
  refine ⟨hd, he, ?_⟩
  by_contra hred
  have hl : g.leadingCoeff = Polynomial.C (φ (universalPlaneLeading f)) := by
    rw [bivariate_leadingCoeff_eq_constant g (by omega)]
    congr 1
    change (g.coeff g.natDegree).coeff 0 = _
    rw [hd]
    exact bivariateMap_coeff φ _ _ _
  have hr := closedForm_rank_drop_of_constant_leading_charZero f.totalDegree hpos
    _ hh.1 g hl hred hd ht
  have hdet : ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det ≠ 0 := by
    rw [← closedForm_minor_map]
    exact hh.2
  have hrank := Matrix.rank_submatrix_le (closedFormCoefficientMatrix f.totalDegree g) rows cols
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hrank
  omega

/-- Construct an integer plane specialization which is geometrically
 irreducible of full degree and avoids an additional algebraic condition.
 The parameter bound is independent of the equation's coefficient height. -/
theorem exists_integer_geometrically_good_plane_avoiding {σ : Type*} [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree)
    (P : MvPolynomial (PlaneParameters (Option σ)) ℤ) (hP : P ≠ 0) :
    ∃ v : PlaneParameters (Option σ) → ℤ,
      (∀ i, 0 ≤ v i ∧ v i ≤ 2 * f.totalDegree ^ 3 + P.totalDegree) ∧
      eval v P ≠ 0 ∧
      (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)).natDegree =
        f.totalDegree ∧
      bivariateTotalDegree
          (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)) =
        f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  obtain ⟨rows, cols, _, _, hW, hdegree⟩ := exists_integer_universalPlane_badWitness f hir hd
  let W := universalPlaneBadWitness f rows cols
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero (W * P) (mul_ne_zero hW hP)
    (2 * f.totalDegree ^ 3 + P.totalDegree)
    ((totalDegree_mul W P).trans (Nat.add_le_add_right hdegree _))
  rw [eval_mul] at hvalue
  obtain ⟨hvW, hvP⟩ := mul_ne_zero_iff.mp hvalue
  let φ := (Int.castRingHom (AlgebraicClosure ℚ)).comp (eval v)
  have hwφ : φ W ≠ 0 := by
    simpa only [φ, RingHom.comp_apply, Int.coe_castRingHom, ne_eq, Int.cast_eq_zero] using hvW
  have hgood := universalPlaneBadWitness_good_specialization_charZero f hd rows cols φ hwφ
  refine ⟨v, hv, hvP, ?_⟩
  simpa only [φ, bivariateMap_comp_apply, universalPlaneSection] using hgood

end
end CCDN
