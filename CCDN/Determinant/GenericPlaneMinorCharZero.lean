/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfacePositioningCharZero
/-! A nonzero slope minor in characteristic zero, with ordinary and geometric
irreducibility constructed from the smooth generic-plane family. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix MvPolynomial

theorem exists_closedForm_minor_of_smooth_plane_point_charZero
    {K : Type*} [Field K] [CharZero K]
    (d : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d) :
    ∃ (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective a ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).submatrix a c).det ≠ 0 := by
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
  have hr := closedForm_coefficient_rank_lower d g hgi hgm hgd
  obtain ⟨a, c, ha, hc, hdet⟩ := Matrix.exists_det_submatrix_ne_zero_of_le_rank
    (closedFormCoefficientMatrix d g) (2 * d ^ 2 - 1) (by omega)
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [← closedForm_minor_map, he, map_zero]


theorem exists_genericPlane_minor_charZero
    {K σ : Type*} [Field K] [CharZero K]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    ∃ (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective a ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d (genericPlanePolynomial f)).submatrix a c).det ≠ 0 := by
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let g := genericPlaneMap K F σ f
  have hx : 0 < (optionEquivLeft K σ f).natDegree := hdeg ▸ hd
  have hpos : 0 < f.totalDegree := by
    rw [natDegree_optionEquivLeft] at hx
    exact hx.trans_le (degreeOf_le_totalDegree f none)
  have hgi : Irreducible g := genericPlaneMap_irreducible f hf hpos hm hx
  have hgz : eval (0 : Fin 2 → F) g = 0 := by
    rw [genericPlaneMap_eval_zero, hz, map_zero]
  have hgs : eval (0 : Fin 2 → F) (pderiv 0 g) ≠ 0 := by
    rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    exact (map_ne_zero (algebraMap K F)).mpr hs
  have hgm : (bivariatePolynomialEquiv F g).Monic := by
    rw [genericPlaneMap_bivariate]
    exact bivariateMap_monic φ (genericPlanePolynomial_monic f hm)
  have hgd : (bivariatePolynomialEquiv F g).natDegree = d := by
    rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_closedForm_minor_of_smooth_plane_point_charZero
    d g hgi (0 : Fin 2 → F) 0 hgz hgs hgm hgd
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [genericPlaneMap_bivariate, ← closedForm_minor_map, he, map_zero]


theorem exists_positioned_genericPlane_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
        (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
        Function.Injective rows ∧ Function.Injective cols ∧
        ((closedFormCoefficientMatrix f.totalDegree
          (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix rows cols).det ≠ 0 := by
  obtain ⟨a, b, hb, hdir, hg, hm, hdeg, _, hz, hs⟩ :=
    exists_monic_smooth_hypersurface_coordinates_charZero f hf hpos
  exact ⟨a, b, hb, hdir, exists_genericPlane_minor_charZero f.totalDegree hpos
    (normalizedHypersurfaceCoordinates a b hb f) hg hm hdeg hz hs⟩


end
end CCDN
