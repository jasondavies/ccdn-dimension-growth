/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Projection.ProjectivePlaneProjection
import CCDN.Algebra.ProjectiveChartScalarExtension
import CCDN.Algebra.ProjectiveCoefficientExtension
/-! Projective closure preserves the Hilbert degree and its standard
chart recovers exactly the original affine zero locus. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma projectiveClosureIdeal_not_X_zero {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    X 0 ∉ projectiveClosureIdeal I := by
  rw [homogeneous_mem_projectiveClosureIdeal_iff I _ (isHomogeneous_X K 0)]
  simp only [affineChart, eval₂Hom_X', Fin.cons_zero]
  intro h
  exact Ideal.one_notMem I h

lemma projectiveClosureIdeal_chart {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    projectiveChartIdeal (projectiveClosureIdeal I) = I := by
  ext f
  rw [projectiveChartIdeal_mem_iff_boundedHomogenize _
    (projectiveClosureIdeal_not_X_zero I) f le_rfl,
    homogeneous_mem_projectiveClosureIdeal_iff _ _ (boundedHomogenize_homogeneous f le_rfl),
    affineChart_boundedHomogenize]

/-- Exact equality of all homogeneous and filtered Hilbert functions. -/
theorem projectiveClosureIdeal_hilbertFunction {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (M : ℕ) :
    projectiveHilbertFunction (projectiveClosureIdeal I) M =
      Module.finrank K (filteredCoordinateSpace I M) := by
  let J := projectiveClosureIdeal I
  let q := IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K ⧸ J)
    (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J))
  have h0 : q ((Ideal.Quotient.mk J) (X 0)) ≠ 0 := by
    intro h
    apply projectiveClosureIdeal_not_X_zero I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective (MvPolynomial (Fin (n + 1)) K ⧸ J)
      (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ J))) (by change q ((Ideal.Quotient.mk J) (X 0)) = q 0; simpa only [map_zero] using h)
  have hh := projective_chart_filtered_finrank J q (IsFractionRing.injective _ _) h0 M
  change Module.finrank K (filteredCoordinateSpace (projectiveChartIdeal J) M) = _ at hh
  rw [projectiveClosureIdeal_chart I] at hh
  exact hh.symm

theorem projectiveClosureIdeal_curveDegree {n d : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (hdegree : HasAffineCurveDegree I d) :
    HasProjectiveCurveDegree (projectiveClosureIdeal I) d := by
  obtain ⟨N,c,h⟩ := hdegree
  refine ⟨N,c,?_⟩
  intro M hM
  rw [projectiveClosureIdeal_hilbertFunction]
  exact h M hM

theorem projectiveClosureIdeal_injective {K : Type*} [Field K] {n : ℕ} :
    Function.Injective (@projectiveClosureIdeal K _ n) := by
  intro I J h
  ext f
  have hI := homogeneous_mem_projectiveClosureIdeal_iff I
    (boundedHomogenize f.totalDegree f) (boundedHomogenize_homogeneous f le_rfl)
  have hJ := homogeneous_mem_projectiveClosureIdeal_iff J
    (boundedHomogenize f.totalDegree f) (boundedHomogenize_homogeneous f le_rfl)
  rw [affineChart_boundedHomogenize] at hI hJ
  rw [← hI, ← hJ, h]

lemma projectiveClosureIdeal_chart_point {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (a : Fin n → K) :
    affineProjectivePoint a ∈ projectiveIdealZeroLocus (projectiveClosureIdeal I) ↔
      ∀ f ∈ I, eval a f = 0 := by
  classical
  constructor
  · intro h f hf
    have hmem : boundedHomogenize f.totalDegree f ∈ projectiveClosureIdeal I := by
      rw [homogeneous_mem_projectiveClosureIdeal_iff _ _
        (boundedHomogenize_homogeneous f le_rfl), affineChart_boundedHomogenize]
      exact hf
    have hz := h (Fin.cons 1 a) (affineCoordinateVector_ne_zero a) rfl _ hmem
    rwa [← affineChart_eval, affineChart_boundedHomogenize] at hz
  · intro ha v hv he f hf
    have hvanish : ∀ g ∈ projectiveClosureIdeal I, eval (Fin.cons 1 a) g = 0 := by
      intro g hg
      rw [← sum_homogeneousComponent g, map_sum]
      apply Finset.sum_eq_zero
      intro M _
      rw [← affineChart_eval]
      exact ha _ ((mem_projectiveClosureIdeal_iff I g).mp hg M)
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' K v (Fin.cons 1 a)
      hv (affineCoordinateVector_ne_zero a)).mp he
    rw [← hc]
    exact homogeneous_ideal_eval_smul (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) _ hvanish c f hf

end
end CCDN
