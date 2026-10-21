/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.ChowLinearSpecialization
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Center.BalancedParameterFiniteness
import CCDN.Center.ProjectiveIncidenceClosed
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDN.Hilbert.ScalarExtension

/-! The matrix image commutes with coefficient extension and has
the same Hilbert polynomial after extension. Geometric center avoidance
also proves integrality over the original coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private lemma chowProjectionForms_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {n s : ℕ}
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    (fun i => map φ (chowProjectionForms A i)) = chowProjectionForms (A.map φ) := by
  funext i
  simp [linearForm]

private theorem chowProjectionImageIdeal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    (chowProjectionImageIdeal I A).map (map (algebraMap K L)) =
      chowProjectionImageIdeal (I.map (map (algebraMap K L))) (A.map (algebraMap K L)) := by
  rw [chowProjectionImageIdeal, projection_kernel_scalar_extension, chowProjectionForms_map]
  rfl

/-- The image ideal of the linear projection by the rows of `A`, computed after extending the
coefficients from `K` to `L`, has the same filtered Hilbert polynomial as the image ideal over
`K`. -/
theorem chowProjectionImageIdeal_hilbertPolynomial_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K) :
    filteredHilbertPolynomial
        (chowProjectionImageIdeal (I.map (map (algebraMap K L))) (A.map (algebraMap K L))) =
      filteredHilbertPolynomial (chowProjectionImageIdeal I A) := by
  rw [← chowProjectionImageIdeal_scalar_extension, filteredHilbertPolynomial_scalar_extension]

/-- If the homogeneous ideal `I` has no zero over an algebraically closed extension `L` that lies
in the kernel of `A`, as a projective point, then the projection by the rows of `A` is integral
over the original field `K`. -/
theorem projection_integral_of_geometric_center_disjoint
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : IsHomogeneousIdeal I)
    (A : Matrix (Fin (s + 1)) (Fin (n + 1)) K)
    (hcenter : ∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap K L))),
      (A.map (algebraMap K L)) *ᵥ p.rep ≠ 0) :
    (projectionCoordinateMap I (chowProjectionForms A)).IsIntegral := by
  classical
  apply integral_projection_of_homogeneous_origin_fiber (L := L) I hI _
    (chowProjectionForms_homogeneous A)
  intro x hx
  by_contra hx0
  let J := I.map (map (algebraMap K L))
  have hxJ : x ∈ idealZeroLocus J := by
    have hh : J ≤ RingHom.ker (eval x) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro f hf
      change eval x (map (algebraMap K L) f) = 0
      rw [eval_map]
      exact hx f (Ideal.mem_sup_left hf)
    exact hh
  have hxA : A.map (algebraMap K L) *ᵥ x = 0 := by
    funext i
    have hh := hx (chowProjectionForms A i)
      (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    simpa only [linearForm, map_sum, map_mul, aeval_C, aeval_X,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] using hh
  have hinc : (fun q : Fin (s + 1) × Fin (n + 1) =>
      (A.map (algebraMap K L)) q.1 q.2) ∈ projectiveChowIncidenceLocus (s + 1) J := by
    apply (projectiveChowIncidenceLocus_iff_cone J (homogeneous_ideal_scalar_extension I hI) _).mpr
    exact ⟨x, hx0, hxJ, fun i => congrFun hxA i⟩
  obtain ⟨p, hp, hrel⟩ := hinc
  apply hcenter p hp
  funext i
  exact hrel i

end
end CCDN
