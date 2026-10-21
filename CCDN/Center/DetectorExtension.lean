/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.BirationalCenterLocus
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Center.BirationalCenterLocus
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowRestrictionBirational
import CCDN.Center.GeometricIdealPrimality
import CCDN.Center.ResultantDetector
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDN.Hilbert.ScalarExtension

/-! Sharp equations over the source field detect birational centers
in every coefficient-field extension, including their geometric disjointness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private lemma eval₂_center_minor_map_tower
    {K L E : Type*} [Field K] [Field L] [Field E]
    (φ : K →+* L) (ψ : L →+* E) {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) L) (g : MvPolynomial (Fin r ↪ Fin n) K) :
    eval₂ (ψ.comp φ) (matrixPluckerCoordinates (A.map ψ)) g =
      ψ (eval₂ φ (matrixPluckerCoordinates A) g) := by
  rw [show matrixPluckerCoordinates (A.map ψ) = ψ ∘ matrixPluckerCoordinates A from
    funext (matrixPluckerCoordinates_map ψ A)]
  exact (eval₂_comp_left ψ φ (matrixPluckerCoordinates A) g).symm

/-- A family of minor conditions detects the same `L`-matrices before and after extending the
coefficients along a field tower `K → L → E`. -/
private lemma exists_eval₂_center_minor_map_ne_zero_iff
    {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] {r n : ℕ} (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K))
    (A : Matrix (Fin r) (Fin n) L) :
    (∃ g ∈ Φ, eval₂ (algebraMap K E)
      (matrixPluckerCoordinates (A.map (algebraMap L E))) g ≠ 0) ↔
      ∃ g ∈ Φ, eval₂ (algebraMap K L) (matrixPluckerCoordinates A) g ≠ 0 := by
  rw [IsScalarTower.algebraMap_eq K L E]
  simp only [eval₂_center_minor_map_tower,
    map_ne_zero_iff (algebraMap L E) (algebraMap L E).injective]

/-- Over an algebraically closed field, the Chow restriction along the minor projection matrix
of independent rows is nonzero exactly when the span of the rows misses the variety. -/
private lemma chowLinearSubstitution_centerMinor_ne_zero_iff
    {E : Type*} [Field E] [IsAlgClosed E] {n m r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) E)) [J.IsPrime] (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin r) (Fin (n + 2)) E) (hA : LinearIndependent E A.row)
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
    (G : MvPolynomial (Fin (m + 1) × Fin (n + 2)) E)
    (hzero : ∀ U, eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) :
    chowLinearSubstitution (centerMinorProjectionMatrix A e) G ≠ 0 ↔
      ∀ p ∈ projectiveIdealZeroLocus J, p.rep ∉ Submodule.span E (Set.range A.row) := by
  refine (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdim _ G hzero).trans
    ⟨?_, centerMinorProjectionMatrix_disjoint _ A hA e⟩
  intro h p hp hspan
  apply h p hp
  change p.rep ∈ (centerMinorProjectionMatrix A e).mulVecLin.ker
  rwa [centerMinorProjectionMatrix_ker A hA e]

/-- A finite family of forms over the source field, homogeneous of degree `(m + 1) d (2d - 1)` in
the Plücker coordinates, detects birational centers over every coefficient extension `L`: a matrix
of independent rows is a birational center for the extended prime exactly when one of the forms
does not vanish on its minors. -/
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
  have hJLdimdeg : HasProjectiveDimensionDegree JL m d :=
    hasProjectiveDimensionDegree_scalar_extension hdimdeg
  obtain ⟨F,s,e,Φ,_,hFE,hhom,hdeg,hdet⟩ :=
    exists_center_resultant_forms (L := E) J hJ d hdimdeg hr
  have hmap : map ψ (map φ F) = map θ F := by
    rw [MvPolynomial.map_map]
    congr 1
  have hFL : IsProjectiveChowEquation (JL.map (map ψ)) (map ψ (map φ F)) (fun _ => d) := by
    rw [hmap]
    dsimp only [JL,φ,ψ]
    rw [ideal_scalar_extension_tower]
    exact hFE
  refine ⟨Φ,hhom,hdeg,?_⟩
  intro A hA
  let AE := A.map ψ
  let R := chowLinearSubstitution (centerMinorProjectionMatrix AE e) (map θ F)
  have hAE : LinearIndependent E AE.row := linearIndependent_matrix_rows_map ψ A hA
  have hdetA : (∃ g ∈ Φ, eval₂ φ (matrixPluckerCoordinates A) g ≠ 0) ↔ Irreducible R :=
    (exists_eval₂_center_minor_map_ne_zero_iff Φ A).symm.trans (hdet AE)
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus (JL.map (map ψ)),
      p.rep ∉ Submodule.span E (Set.range AE.row) := by
    have hh := chowLinearSubstitution_centerMinor_ne_zero_iff (JL.map (map ψ))
      (homogeneous_ideal_scalar_extension (L := E) JL hJL)
      (hasProjectiveDimensionDegree_scalar_extension hJLdimdeg).natDegree_eq AE hAE e
      (map ψ (map φ F)) hFL.eval_eq_zero_iff
    rwa [hmap] at hh
  have hbir (hc : ∀ p ∈ projectiveIdealZeroLocus (JL.map (map ψ)),
      p.rep ∉ Submodule.span E (Set.range AE.row)) :
      Irreducible R ↔ projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 2)) L ⧸ JL)) JL
        (centerMinorProjectionForm A) = ⊤ := by
    rw [← projectionImageField_centerMinorProjectionMatrix _ A e]
    have hh := geometric_chow_restriction_irreducible_iff_birational JL hJL d hJLdimdeg
      (map φ F) hFL (centerMinorProjectionMatrix A e)
    rw [centerMinorProjectionMatrix_map,hmap] at hh
    exact hh (centerMinorProjectionMatrix_disjoint _ AE hAE e hc)
  constructor
  · intro hg
    have hir := hdetA.mp hg
    have hc := hcenteriff.mp hir.ne_zero
    exact ⟨hc,(hbir hc).mp hir⟩
  · rintro ⟨hc,hf⟩
    exact hdetA.mpr ((hbir hc).mpr hf)

/-- Extending an ideal of `MvPolynomial σ K` along the identity map `algebraMap K K` gives back the
same ideal. -/
lemma ideal_map_algebraMap_self {K σ : Type*} [Field K] (J : Ideal (MvPolynomial σ K)) :
    J.map (map (algebraMap K K)) = J := by
  have h : (map (algebraMap K K) : MvPolynomial σ K →+* MvPolynomial σ K) = RingHom.id _ := by
    ext <;> simp
  rw [h,Ideal.map_id]

/-- Let `J` be a homogeneous prime ideal over a field `K` of characteristic zero, of projective
dimension `m` and degree `d`, that stays prime over an algebraic closure. There is a finite family
of forms in the Plücker coordinates, homogeneous of degree `(m + 1) d (2d - 1)`, such that a matrix
over `K` with independent rows is a birational center for `J` exactly when one of the forms does
not vanish on its minors. -/
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
