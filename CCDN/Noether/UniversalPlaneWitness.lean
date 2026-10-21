/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.UniversalPlaneFamily
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.UniversalPlaneDegree
import CCDN.Projection.ShearNormalization
import CCDN.ForMathlib.MvPolynomial
/-! A nonzero universal minor of cubic parameter degree, over the original
coefficient field. The nonvanishing proof descends from an algebraic closure. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma universalPlaneMap_map {K L σ : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneMap L σ (MvPolynomial.map φ f) =
      MvPolynomial.map (MvPolynomial.map φ) (universalPlaneMap K σ f) := by
  have he : (universalPlaneMap L σ).toRingHom.comp (MvPolynomial.map φ) =
      (MvPolynomial.map (MvPolynomial.map φ)).comp (universalPlaneMap K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalPlaneMap]
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

lemma universalPlanePolynomial_map {K L σ : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlanePolynomial (MvPolynomial.map φ f) =
      bivariateMap (MvPolynomial.map φ) (universalPlanePolynomial f) := by
  rw [universalPlanePolynomial, universalPlaneMap_map, universalPlanePolynomial,
    bivariatePolynomialEquiv_map]

/-- A geometrically irreducible equation yields a nonzero polynomial
in the full affine-plane parameter ring, of degree at most (2*d^2-1)*d.
There are no smoothness or positioning hypotheses on the input equation. -/
theorem exists_universalPlane_minor_degree
    {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      Function.Injective rows ∧ Function.Injective cols ∧
      ((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 ∧
      (((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det).totalDegree ≤
          (2 * f.totalDegree ^ 2 - 1) * f.totalDegree := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hex := exists_universalPlane_minor
    (MvPolynomial.map φ f) hf (ht ▸ hpos) (ht ▸ hchar.map φ)
  rw [ht] at hex
  obtain ⟨rows, cols, hr, hc, hdet⟩ := hex
  refine ⟨rows, cols, hr, hc, ?_, ?_⟩
  · intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  · exact closedForm_minor_parameterDegree _ _ _ _
      (universalPlanePolynomial_coefficient_degree f) rows cols

end
end CCDN
