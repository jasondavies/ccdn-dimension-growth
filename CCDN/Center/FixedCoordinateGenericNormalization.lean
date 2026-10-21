/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.LinearForm
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Center.ClosureNormalizationInfinite
import CCDN.Center.GenericLinearNormalizationOpenness
/-! Generic affine linear normalization with the homogenizing coordinate
fixed. The finite specialization and its nonzero determinant are both
constructed from the source ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The family of linear forms whose coefficient rows are `u (i, ·)`. -/
abbrev genericAffineParameterForms {R : Type*} [CommRing R] {m n : ℕ}
    (u : Fin m × Fin n → R) : Fin m → MvPolynomial (Fin n) R :=
  fun i => linearForm fun j => u (i,j)

lemma genericAffineParameterForms_homogeneous {R : Type*} [CommRing R] {m n : ℕ}
    (u : Fin m × Fin n → R) (i : Fin m) :
    (genericAffineParameterForms u i).IsHomogeneous 1 :=
  linearForm_isHomogeneous _

lemma homogeneous_linear_forms_coefficient_representation
    {K : Type*} [Field K] {m n : ℕ} (a : Fin m → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1) :
    ∃ c : Fin m × Fin n → K, genericAffineParameterForms c = a := by
  classical
  have hspan (i) : a i ∈ Submodule.span K (Set.range (X : Fin n → MvPolynomial (Fin n) K)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact ha i
  have hex (i) := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan i)
  choose c hc using hex
  refine ⟨fun q => c q.1 q.2, ?_⟩
  funext i
  simpa only [linearForm, smul_eq_C_mul] using hc i

def genericFixedCoordinateFamily (K : Type*) [Field K] (m n : ℕ) :
    Fin (m + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m × Fin n) K) :=
  Fin.cons (X 0) (fun i => ∑ j, C (X (i,j)) * X j.succ)

lemma genericFixedCoordinateFamily_homogeneous
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + 1)) :
    (genericFixedCoordinateFamily K m n i).IsHomogeneous 1 := by
  refine Fin.cases (isHomogeneous_X _ _) (fun j => ?_) i
  exact IsHomogeneous.sum _ _ _ (fun k _ => isHomogeneous_C_mul_X _ _)

lemma genericFixedCoordinateFamily_map
    {K L : Type*} [Field K] [Field L] {m n : ℕ}
    (φ : MvPolynomial (Fin m × Fin n) K →+* L) :
    (fun i => map φ (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates (genericAffineParameterForms (fun q => φ (X q))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [genericFixedCoordinateFamily, closureProjectionCoordinates]
  · simp [genericFixedCoordinateFamily, closureProjectionCoordinates, linearForm]

/-- Independent coefficients give a finite normalization of the
projective closure while its homogenizing coordinate remains fixed. -/
theorem generic_fixed_coordinate_projection_integral
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin m × Fin n → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
      (closureProjectionCoordinates (genericAffineParameterForms u))).IsIntegral := by
  obtain ⟨_,_,hbound,_⟩ := filteredHilbertPolynomial_positive_multiplicity I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  have hmn : m ≤ n := by simpa only [hm, Fintype.card_fin] using hbound
  obtain ⟨a,ha,_,_,hint⟩ := exists_closure_normalization_infinite_of_le m n hmn I hm
  obtain ⟨c,hc⟩ := homogeneous_linear_forms_coefficient_representation a ha
  have hspecial : (fun i => map (eval c) (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates a := by
    rw [genericFixedCoordinateFamily_map]
    simpa only [eval_X] using congrArg closureProjectionCoordinates hc
  have hgeneric : (fun i => map (aeval u).toRingHom (genericFixedCoordinateFamily K m n i)) =
      closureProjectionCoordinates (genericAffineParameterForms u) := by
    rw [genericFixedCoordinateFamily_map]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  have h := generic_linear_projection_integral_of_specialization
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I)
    (genericFixedCoordinateFamily K m n) (genericFixedCoordinateFamily_homogeneous K m n)
    c (by rwa [hspecial]) u hu
  rwa [projectiveClosureIdeal_scalar_extension, hgeneric] at h

end
end CCDN
