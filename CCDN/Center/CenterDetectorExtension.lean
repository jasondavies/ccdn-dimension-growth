/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.BirationalCenterLocus
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.CenterResultantDetector
import CCDN.Center.ChowProjectionBaseChange
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowRestrictionBirational
import CCDN.Center.GeometricIdealPrimality
import CCDN.Hilbert.HilbertScalarExtension
import CCDN.Hilbert.HomogeneousPrimeComponents
/-! Sharp equations over the source field detect birational centers
in every coefficient-field extension, including their geometric disjointness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma eval₂_center_minor_map_tower
    {K L E : Type*} [Field K] [Field L] [Field E]
    (φ : K →+* L) (ψ : L →+* E) {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) L) (g : MvPolynomial (Fin r ↪ Fin n) K) :
    eval₂ (ψ.comp φ) (matrixPluckerCoordinates (A.map ψ)) g =
      ψ (eval₂ φ (matrixPluckerCoordinates A) g) := by
  rw [show matrixPluckerCoordinates (A.map ψ) = ψ ∘ matrixPluckerCoordinates A from
    funext (matrixPluckerCoordinates_map ψ A)]
  exact (eval₂_comp_left ψ φ (matrixPluckerCoordinates A) g).symm

theorem exists_extended_birational_center_detector
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
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
        IsBirationalMatrixCenter (J.map (map (algebraMap K L))) A := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let E := AlgebraicClosure L
  let φ := algebraMap K L
  let ψ := algebraMap L E
  let θ := algebraMap K E
  let JL := J.map (map φ)
  have hJE : (J.map (map (algebraMap K E))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  have hJLE : (JL.map (map (algebraMap L E))).IsPrime := by
    dsimp only [JL,φ]
    rw [ideal_scalar_extension_tower]
    exact hJE
  have hJL := homogeneous_ideal_scalar_extension (L := L) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  have hJLdegree : (filteredHilbertPolynomial JL).leadingCoeff = (d : ℚ) / (m + 1).factorial := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdegree
  obtain ⟨F,s,e,Φ,_,hFE,hδ,hzero,hhom,hdeg,hdet⟩ :=
    exists_center_resultant_forms (L := E) J hJ d ⟨hdim, hdegree⟩ hr
  have hmap : map ψ (map φ F) = map θ F := by
    rw [MvPolynomial.map_map]
    congr 1
  have hδL (i) : (map φ F).IsWeightedHomogeneous (chowRowWeight i) d := by
    intro a ha
    apply hδ i
    intro hz
    apply ha
    rw [coeff_map,hz,map_zero]
  have hzeroL : ∀ U, eval U (map ψ (map φ F)) = 0 ↔
      U ∈ projectiveChowIncidenceLocus (m + 1) (JL.map (map ψ)) := by
    rw [hmap]
    dsimp only [JL,φ,ψ]
    rw [ideal_scalar_extension_tower]
    exact hzero
  refine ⟨Φ,hhom,hdeg,?_⟩
  intro A hA
  let AE := A.map ψ
  let M := centerMinorProjectionMatrix AE e
  let R := chowLinearSubstitution M (map θ F)
  have hAE : LinearIndependent E AE.row := linearIndependent_matrix_rows_map ψ A hA
  have hdetA : (∃ g ∈ Φ, eval₂ φ
      (matrixPluckerCoordinates A) g ≠ 0) ↔ Irreducible R := by
    have hh := hdet AE
    have ht : θ = ψ.comp φ := IsScalarTower.algebraMap_eq K L E
    change (∃ g ∈ Φ, eval₂ θ _ g ≠ 0) ↔ _ at hh
    rw [ht] at hh
    simpa only [AE,eval₂_center_minor_map_tower,map_ne_zero_iff ψ ψ.injective] using hh
  have hJEE := homogeneous_ideal_scalar_extension (L := E) JL hJL
  have hJEEdim : (filteredHilbertPolynomial (JL.map (map ψ))).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hJLdim
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus (JL.map (map ψ)),
      p.rep ∉ Submodule.span E (Set.range AE.row) := by
    have hh := chowLinearSubstitution_ne_zero_iff_center_disjoint
      (JL.map (map ψ)) hJEE hJEEdim M (map ψ (map φ F)) hzeroL
    rw [hmap] at hh
    refine hh.trans ⟨?_,centerMinorProjectionMatrix_disjoint _ AE hAE e⟩
    intro h p hp hspan
    apply h p hp
    change p.rep ∈ M.mulVecLin.ker
    rwa [centerMinorProjectionMatrix_ker AE hAE e]
  have hbir (hc : ∀ p ∈ projectiveIdealZeroLocus (JL.map (map ψ)),
      p.rep ∉ Submodule.span E (Set.range AE.row)) :
      Irreducible R ↔ projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 2)) L ⧸ JL)) JL
        (centerMinorProjectionForm A) = ⊤ := by
    rw [← projectionImageField_centerMinorProjectionMatrix _ A e]
    have hh := geometric_chow_restriction_irreducible_iff_birational JL hJL d ⟨hJLdim, hJLdegree⟩
      (map φ F) (hmap.symm ▸ hFE) hδL hzeroL (centerMinorProjectionMatrix A e)
    rw [centerMinorProjectionMatrix_map,hmap] at hh
    exact hh (centerMinorProjectionMatrix_disjoint _ AE hAE e hc)
  constructor
  · intro hg
    have hir := hdetA.mp hg
    have hc := hcenteriff.mp hir.ne_zero
    exact ⟨hc,(hbir hc).mp hir⟩
  · rintro ⟨hc,hf⟩
    exact hdetA.mpr ((hbir hc).mpr hf)

lemma ideal_map_algebraMap_self {K σ : Type*} [Field K] (J : Ideal (MvPolynomial σ K)) :
    J.map (map (algebraMap K K)) = J := by
  have h : (map (algebraMap K K) : MvPolynomial σ K →+* MvPolynomial σ K) = RingHom.id _ := by
    ext <;> simp
  rw [h,Ideal.map_id]

/-- The detector over the source field itself. -/
theorem exists_birational_center_detector
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d)
    (hr : r + 2 ≤ n + 2) :
    ∃ Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      ∀ (A : Matrix (Fin r) (Fin (n + 2)) K) (_ : LinearIndependent K A.row),
        (∃ g ∈ Φ, eval (matrixPluckerCoordinates A) g ≠ 0) ↔ IsBirationalMatrixCenter J A := by
  have : (J.map (map (algebraMap K K))).IsPrime := by
    rw [ideal_map_algebraMap_self]
    infer_instance
  obtain ⟨Φ,hhom,hdeg,hdet⟩ :=
    exists_extended_birational_center_detector (L := K) J hJ d hdimdeg hr
  refine ⟨Φ,hhom,hdeg,fun A hA => ?_⟩
  rw [← isBirationalMatrixCenter_congr (ideal_map_algebraMap_self J)]
  refine Iff.trans ?_ (hdet A hA)
  rw [Algebra.algebraMap_self]
  rfl

end
end CCDN
