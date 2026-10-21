/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Determinant.GenericPlaneSmoothness
public import CCDN.ForMathlib.MatrixRank
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.SmoothPlaneMinor
/-! A nonzero polynomial determinant in the generic slope parameters. For a
positioned irreducible equation with a smooth origin, the minor is constructed
over the parameter polynomial ring, by descent from its fraction field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma genericPlaneMap_totalDegree_le {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    (genericPlaneMap K F σ f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i with
  | none => simp
  | some i => exact (totalDegree_mul _ _).trans (by simp)

/-- Over the fraction field of the slope ring, the generic plane of a positioned irreducible
equation with a smooth origin is irreducible, smooth at the origin in the first coordinate,
and monic of the same outer degree. -/
lemma genericPlaneMap_smooth_monic {K σ : Type*} [Field K]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    Irreducible (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) ∧
      eval 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) = 0 ∧
      eval 0 (pderiv 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)) ≠ 0 ∧
      (bivariatePolynomialEquiv _
        (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)).Monic ∧
      (bivariatePolynomialEquiv _
        (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)).natDegree = d := by
  let F := FractionRing (MvPolynomial σ K)
  let φ : MvPolynomial σ K →+* F := algebraMap (MvPolynomial σ K) F
  have hx : 0 < (optionEquivLeft K σ f).natDegree := hdeg ▸ hd
  have hpos : 0 < f.totalDegree := by
    rw [natDegree_optionEquivLeft] at hx
    exact hx.trans_le (degreeOf_le_totalDegree f none)
  refine ⟨genericPlaneMap_irreducible f hf hpos hm hx, ?_, ?_, ?_, ?_⟩
  · rw [genericPlaneMap_eval_zero, hz, map_zero]
  · rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    exact (map_ne_zero (algebraMap K F)).mpr hs
  · rw [genericPlaneMap_bivariate]
    exact bivariateMap_monic φ (genericPlanePolynomial_monic f hm)
  · rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]

/-- In characteristic zero or greater than 2*d^2, a positioned irreducible hypersurface
with a smooth origin supplies a nonzero minor polynomial in its plane slopes. -/
theorem exists_genericPlane_minor
    {K σ : Type*} [Field K]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2))
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (closedFormCoefficientMatrix d (genericPlanePolynomial f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let F := FractionRing (MvPolynomial σ K)
  obtain ⟨hgi, hgz, hgs, hgm, hgd⟩ := genericPlaneMap_smooth_monic d hd f hf hm hdeg hz hs
  obtain ⟨a, c, hdet⟩ := exists_closedForm_minor_of_smooth_plane_point d _ hgi 0 0
    hgz hgs hgm hgd ((genericPlaneMap_totalDegree_le f).trans htotal)
    (hchar.map (algebraMap K F))
  refine ⟨a, c, fun he ↦ hdet ?_⟩
  rw [genericPlaneMap_bivariate, ← closedForm_minor_map, he, map_zero]

end
end CCDN
