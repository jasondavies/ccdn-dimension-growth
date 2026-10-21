/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.CenterMinorMatrix
public import CCDN.Center.ChowIncidenceGrading
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowRowResultantCriterion
import CCDN.Center.ChowRowSymmetry
import CCDN.Center.ClosedFieldChowBirationalCriterion
import CCDN.Center.ProjectiveChowExactDegree
import CCDN.Determinant.SingularDeterminant
import CCDN.Hilbert.HilbertScalarExtension
import CCDN.Hilbert.HomogeneousPrimeComponents
/-! Sharp-degree resultant detectors defined over the source field and
valid on all centers over an algebraically closed extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_center_resultant_forms
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (hr : r + 2 ≤ n + 2) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
      (s : ℕ) (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      Irreducible F ∧ Irreducible (map (algebraMap K L) F) ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) d) ∧
      (∀ U, eval U (map (algebraMap K L) F) = 0 ↔
        U ∈ projectiveChowIncidenceLocus (m + 1) (J.map (map (algebraMap K L)))) ∧
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 2)) L,
        (∃ g ∈ Φ, eval₂ (algebraMap K L)
          (matrixPluckerCoordinates A) g ≠ 0) ↔
          Irreducible (chowLinearSubstitution (centerMinorProjectionMatrix A e)
            (map (algebraMap K L) F)) := by
  classical
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let φ := algebraMap K L
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := L) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  obtain ⟨F,hF,hFL,hδ,hFdegree,hzero⟩ :=
    exists_geometric_projective_chow_exact_degree (L := L) J hJ d ⟨hdim, hdegree⟩
  obtain ⟨s,⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  have hd : 0 < d := by
    have hp := irreducible_mvPolynomial_totalDegree_pos hF
    rw [hFdegree] at hp
    by_contra hh
    have hz : d = 0 := by omega
    simp only [hz,mul_zero,lt_self_iff_false] at hp
  have hFhom : F.IsHomogeneous ((m + 1) * d) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      chow_rows_homogeneous_total_degree F (fun _ => d) hδ
  let i : Fin (m + 1) := Fin.last m
  let Φ := centerRowResultantFamily e i F d
  refine ⟨F,s,e,Φ,hF,hFL,hδ,hzero,
    centerRowResultantFamily_homogeneous e i F d hd hFhom,
    centerRowResultantFamily_totalDegree_le e i F d hd hFhom,?_⟩
  intro A
  have hrow : (map φ F).IsWeightedHomogeneous (chowRowWeight i) d := by
    intro a ha
    apply hδ i
    intro hz
    apply ha
    rw [coeff_map,hz,map_zero]
  exact (centerRowResultantFamily_nonvanishing_iff_extension φ e i F d A).trans
    (chowRowResultant_ne_zero_iff_irreducible JL hJL hJLdim
      (centerMinorProjectionMatrix A e) (map φ F) hzero i d hd hrow)

/-- A finite family over K detects every disjoint birational center
over the algebraically closed extension L. -/
theorem exists_geometric_center_detector
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (hr : r + 2 ≤ n + 2) :
    ∃ Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      ∀ (A : Matrix (Fin r) (Fin (n + 2)) L) (_ : LinearIndependent L A.row),
        (∃ g ∈ Φ, eval₂ (algebraMap K L)
          (matrixPluckerCoordinates A) g ≠ 0) ↔
        (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap K L))),
          p.rep ∉ Submodule.span L (Set.range A.row)) ∧
        projectionImageField
          (F := FractionRing (MvPolynomial (Fin (n + 2)) L ⧸ J.map (map (algebraMap K L))))
          (J.map (map (algebraMap K L))) (centerMinorProjectionForm A) = ⊤ := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let φ := algebraMap K L
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := L) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  have hJLdegree : (filteredHilbertPolynomial JL).leadingCoeff = (d : ℚ) / (m + 1).factorial := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdegree
  obtain ⟨F,s,e,Φ,_,hFL,hδ,hzero,hhom,hdeg,hdet⟩ :=
    exists_center_resultant_forms (L := L) J hJ d ⟨hdim, hdegree⟩ hr
  have hδL (i) : (map φ F).IsWeightedHomogeneous (chowRowWeight i) d := by
    intro a ha
    apply hδ i
    intro hz
    apply ha
    rw [coeff_map,hz,map_zero]
  refine ⟨Φ,hhom,hdeg,?_⟩
  intro A hA
  rw [← projectionImageField_centerMinorProjectionMatrix _ A e]
  let M := centerMinorProjectionMatrix A e
  let R := chowLinearSubstitution M (map φ F)
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span L (Set.range A.row) := by
    have hh := chowLinearSubstitution_ne_zero_iff_center_disjoint JL hJL hJLdim M (map φ F) hzero
    refine hh.trans ⟨?_,centerMinorProjectionMatrix_disjoint JL A hA e⟩
    intro h p hp hspan
    apply h p hp
    change p.rep ∈ M.mulVecLin.ker
    rwa [centerMinorProjectionMatrix_ker A hA e]
  have hbir (hc : ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span L (Set.range A.row)) :
      Irreducible R ↔ projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 2)) L ⧸ JL)) JL
        (chowProjectionForms M) = ⊤ :=
    chow_restriction_irreducible_iff_birational_over_closed_field JL hJL d ⟨hJLdim, hJLdegree⟩
      (map φ F) hFL hδL hzero M (centerMinorProjectionMatrix_disjoint JL A hA e hc)
  constructor
  · intro hg
    have hir := (hdet A).mp hg
    have hc := hcenteriff.mp hir.ne_zero
    exact ⟨hc,(hbir hc).mp hir⟩
  · rintro ⟨hc,hf⟩
    exact (hdet A).mpr ((hbir hc).mpr hf)

end
end CCDN
