/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfacePositioningCharZero
public import CCDN.Noether.EulerPairSpecialization
/-! Nonzero Euler minors in smooth generic-plane families. The order is
exactly d²−1, and the smooth-point argument constructs the geometric
irreducibility needed by the characteristic-zero closed-form theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix MvPolynomial

theorem exists_euler_minor_of_smooth_plane_point_charZero
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = k + 2) :
    ∃ (a : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (c : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      Function.Injective a ∧ Function.Injective c ∧
      ((eulerClosedFormCoefficientMatrix k (bivariatePolynomialEquiv K f)).submatrix a c).det ≠ 0 := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp only [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm : g.Monic := bivariateMap_monic φ hm
  have hgd : g.natDegree = k + 2 := by
    rw [bivariateMap_natDegree_of_monic φ hm, hdeg]
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_eulerClosedForm_nonzero_minor k g hgi
    1 one_ne_zero (by simpa using hgm.leadingCoeff) hgd
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [← eulerClosedForm_minor_map, he, map_zero]

theorem exists_genericPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = k + 2)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    ∃ (a : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
      (c : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
      Function.Injective a ∧ Function.Injective c ∧
      ((eulerClosedFormCoefficientMatrix k (genericPlanePolynomial f)).submatrix a c).det ≠ 0 := by
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let g := genericPlaneMap K F σ f
  have hx : 0 < (optionEquivLeft K σ f).natDegree := by omega
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
  have hgd : (bivariatePolynomialEquiv F g).natDegree = k + 2 := by
    rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_euler_minor_of_smooth_plane_point_charZero
    k g hgi (0 : Fin 2 → F) 0 hgz hgs hgm hgd
  refine ⟨a, c, ha, hc, ?_⟩
  intro he
  apply hdet
  rw [genericPlaneMap_bivariate, ← eulerClosedForm_minor_map, he, map_zero]

theorem exists_positioned_genericPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      ∃ (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
        (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k),
        Function.Injective rows ∧ Function.Injective cols ∧
        ((eulerClosedFormCoefficientMatrix k
          (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix rows cols).det ≠ 0 := by
  obtain ⟨a, b, hb, hdir, hg, hm, hdeg, _, hz, hs⟩ :=
    exists_monic_smooth_hypersurface_coordinates_charZero f hf (by omega)
  rw [hd] at hdeg
  exact ⟨a, b, hb, hdir, exists_genericPlane_euler_minor_charZero k
    (normalizedHypersurfaceCoordinates a b hb f) hg hm hdeg hz hs⟩

end
end CCDN
