/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.IntegerLinearForms
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Center.GeometricProjectionCenter
/-! Rational row matrices for the constructed geometric projection
center. The rows form a basis of the kernel, and their scalar extension
remains disjoint from the full projective source. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_submodule_basis_matrix
    {K : Type*} [Field K] {r n : ℕ}
    (S : Submodule K (Fin n → K)) (hr : Module.finrank K S = r) :
    ∃ A : Matrix (Fin r) (Fin n) K,
      LinearIndependent K A.row ∧ Submodule.span K (Set.range A.row) = S := by
  classical
  let b := Module.finBasisOfFinrankEq K S hr
  let A : Matrix (Fin r) (Fin n) K := fun i => (b i).val
  refine ⟨A, b.linearIndependent.map' S.subtype (Submodule.ker_subtype S), ?_⟩
  change Submodule.span K (Set.range (fun i => (b i).val)) = S
  have hh := congrArg (Submodule.map S.subtype) b.span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply] using hh

lemma matrix_rows_map_span_le_kernel
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r s n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (B : Matrix (Fin s) (Fin n) K)
    (hker : Submodule.span K (Set.range A.row) ≤ B.mulVecLin.ker) :
    Submodule.span L (Set.range (A.map φ).row) ≤ (B.map φ).mulVecLin.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hk : B *ᵥ A.row i = 0 :=
    hker (Submodule.subset_span (Set.mem_range_self i))
  change (B.map φ) *ᵥ (A.map φ).row i = 0
  funext j
  have hh := congrArg φ (congrFun hk j)
  simpa only [Matrix.mulVec, dotProduct, Matrix.row_apply, Matrix.map_apply,
    map_sum, map_mul, Pi.zero_apply, map_zero] using hh

/-- A basis of the constructed rational birational projection
center. Scalar extension of its row span is disjoint from the
projective variety. -/
theorem exists_geometric_center_row_witness
    {L : Type*} [Field L] [Algebra ℚ L] [Infinite L]
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (n + 1) → ℤ)
      (A : Matrix (Fin (n - m - 1)) (Fin (n + 1)) ℚ),
      LinearIndependent ℚ A.row ∧
      Submodule.span ℚ (Set.range A.row) =
        (Matrix.mulVecLin (fun i j => (b i j : ℚ))).ker ∧
      (∀ p ∈ projectiveIdealZeroLocus (I.map (map (algebraMap ℚ L))),
        p.rep ∉ Submodule.span L (Set.range (A.map (algebraMap ℚ L)).row)) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ := by
  obtain ⟨b, S, _, _, hS, hdimS, _, hdisjoint, hP, _⟩ :=
    exists_geometric_birational_projection_center (L := L) m n hmn I hI d hdimdeg
  obtain ⟨A, hA, hspan⟩ := exists_submodule_basis_matrix S hdimS
  have hker : Submodule.span ℚ (Set.range A.row) =
      (Matrix.mulVecLin (fun i j => (b i j : ℚ))).ker := hspan.trans hS
  refine ⟨b, A, hA, hker, ?_, hP.integral, hP.birational⟩
  have hkerL := matrix_rows_map_span_le_kernel (algebraMap ℚ L) A
    (Matrix.of fun i j => (b i j : ℚ)) hker.le
  intro p hp hmem
  apply hdisjoint p hp
  have hh := hkerL hmem
  change (Matrix.of (fun i j => (b i j : ℚ))).map (algebraMap ℚ L) *ᵥ p.rep = 0 at hh
  have he : (Matrix.of (fun i j => (b i j : ℚ))).map (algebraMap ℚ L) =
      Matrix.of (fun i j => (b i j : L)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_intCast]
  rw [he] at hh
  exact hh

end
end CCDN
