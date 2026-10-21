/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.CenterMinorMatrix
public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Center.CenterResultantForms
public import CCDN.Center.ResultantCoefficientFamily
public import CCDN.Center.GenericBlockLine
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CCDN.Center.ChowProjectionCriterion
import CCDN.Center.ChowRowSymmetry
import CCDN.Center.ClosedFieldChowBirationalCriterion
import CCDN.Center.ProjectiveChowExactDegree
import CCDN.Determinant.SingularDeterminant
import CCDN.Hilbert.HilbertScalarExtension
import CCDN.Hilbert.HomogeneousPrimeComponents
import CCDN.ForMathlib.MvPolynomial
import CCDN.Center.ChowProjectionPower
import CCDN.Center.ProjectiveChowWithoutChart
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Center.ChowPolynomialPower
import CCDN.Center.GenericBlockLineIrreducible

/-!
Sharp-degree resultant detectors defined over the source field and
valid on all centers over an algebraically closed extension.

The selected-row derivative resultant detects irreducibility of a
Chow restriction. A nonzero restriction is a power of the constructed image
Chow equation, so separability is exactly the absence of a repeated power.

When a polynomial has the same hypersurface as an irreducible equation,
a generic block-line derivative resultant detects its irreducibility.
The positive block degree is the degree of the line polynomial.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem genericBlockLine_derivativeResultant_irreducible_iff
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Finite σ]
    (b : σ → Bool) (G R : MvPolynomial σ K) (hG : Irreducible G)
    (hzero : ∀ z : σ → K, eval z R = 0 ↔ eval z G = 0)
    (d : ℕ) (hd : 0 < d)
    (hdegree : R.weightedTotalDegree (genericBlockWeight b) = d) :
    derivativeResultant (genericBlockLine b R) d ≠ 0 ↔ Irreducible R := by
  let A := MvPolynomial (σ ⊕ σ) K
  let F := FractionRing A
  let θ : A →+* F := algebraMap A F
  let ρ : MvPolynomial σ K →+* Polynomial F :=
    (Polynomial.mapRingHom θ).comp (genericBlockLine b)
  have hρdegree : (ρ R).natDegree = d := by
    change ((genericBlockLine b R).map θ).natDegree = d
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A F),
      genericBlockLine_natDegree, hdegree]
  have hresult : derivativeResultant (genericBlockLine b R) d ≠ 0 ↔ (ρ R).Separable := by
    have hh := derivativeResultant_ne_zero_iff_separable (ρ R) d hd hρdegree
    change derivativeResultant ((genericBlockLine b R).map θ) d ≠ 0 ↔ _ at hh
    rw [derivativeResultant_map] at hh
    exact (map_ne_zero_iff θ (IsFractionRing.injective A F)).symm.trans hh
  rw [hresult]
  constructor
  · intro hsep
    obtain ⟨a,r,ha,hr,he⟩ := polynomial_eq_scalar_pow_of_same_zeros G R hG hzero
    have hunit : IsUnit (C a : MvPolynomial σ K) := (isUnit_iff_ne_zero.mpr ha).map C
    have hnot : ¬ IsUnit (ρ G) := by
      intro hunitG
      have hunitR : IsUnit (ρ R) := by
        rw [he,map_mul,map_pow]
        exact (hunit.map ρ).mul (hunitG.pow r)
      have hz := Polynomial.natDegree_eq_zero_of_isUnit hunitR
      omega
    have hpow : ((ρ G) ^ r).Separable := by
      rw [he,map_mul,map_pow] at hsep
      exact hsep.of_mul_right
    have hr1 := (Polynomial.Separable.of_pow hnot (Nat.ne_zero_of_lt hr) hpow).2
    rw [he,hr1,pow_one]
    exact (irreducible_isUnit_mul hunit).mpr hG
  · intro hR
    exact genericBlockLine_fraction_separable (F := F) b R hR (by omega)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem chowRowResultant_ne_zero_iff_irreducible
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n s m : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (A : Matrix (Fin (s + 2)) (Fin (n + 2)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
    (hzero : ∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J)
    (i : Fin (m + 1)) (d : ℕ) (hd : 0 < d)
    (hrow : F.IsWeightedHomogeneous (chowRowWeight i) d) :
    derivativeResultant (genericBlockLine (chowRowBlock i) (chowLinearSubstitution A F)) d ≠ 0 ↔
      Irreducible (chowLinearSubstitution A F) := by
  let R := chowLinearSubstitution A F
  by_cases hR : R = 0
  · change derivativeResultant (genericBlockLine (chowRowBlock i) R) d ≠ 0 ↔ Irreducible R
    rw [hR,map_zero,derivativeResultant_zero d hd]
    simp
  have hcenter := (chowLinearSubstitution_ne_zero_iff_center_disjoint J hJ hdim A F hzero).mp hR
  let P := chowProjectionImageIdeal J A
  have : P.IsPrime := RingHom.ker_isPrime (projectionCoordinateMap J (chowProjectionForms A)).toRingHom
  have hint := chow_projection_integral_of_center_disjoint J hJ A hcenter
  have hPdim : (filteredHilbertPolynomial P).natDegree = m + 1 :=
    (integral_projection_hilbert_dimension_eq J _ hint).trans hdim
  obtain ⟨G,_,hG,_,hGzero⟩ := exists_projective_chow_equation_without_chart P
    (chowProjectionImageIdeal_homogeneous J hJ A) hPdim
  have hsame := chowLinearSubstitution_same_zeros_as_image J hJ A hcenter F G hzero hGzero
  have hdeg : R.weightedTotalDegree (genericBlockWeight (chowRowBlock i)) = d := by
    rw [genericBlockWeight_chowRowBlock]
    exact weightedTotalDegree_of_nonzero_homogeneous _ _ d
      (chowLinearSubstitution_row_homogeneous A i F d hrow) hR
  exact genericBlockLine_derivativeResultant_irreducible_iff
    (chowRowBlock i) G R hG hsame d hd hdeg

end
end CCDN

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
      Irreducible F ∧
      IsProjectiveChowEquation (J.map (map (algebraMap K L))) (map (algebraMap K L) F)
        (fun _ => d) ∧
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 2)) L,
        (∃ g ∈ Φ, eval₂ (algebraMap K L)
          (matrixPluckerCoordinates A) g ≠ 0) ↔
          Irreducible (chowLinearSubstitution (centerMinorProjectionMatrix A e)
            (map (algebraMap K L) F)) := by
  classical
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let φ := algebraMap K L
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := L) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 :=
    (hasProjectiveDimensionDegree_scalar_extension hdimdeg).natDegree_eq
  obtain ⟨F,hF,hFL,hδ,hFdegree,hzero⟩ :=
    exists_geometric_projective_chow_exact_degree (L := L) J hJ d hdimdeg
  obtain ⟨s,⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  have hd : 0 < d := by
    have hp := MvPolynomial.totalDegree_pos_of_irreducible hF
    rw [hFdegree] at hp
    by_contra hh
    have hz : d = 0 := by omega
    simp only [hz,mul_zero,lt_self_iff_false] at hp
  have hFhom : F.IsHomogeneous ((m + 1) * d) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      chow_rows_homogeneous_total_degree F (fun _ => d) hδ
  let i : Fin (m + 1) := Fin.last m
  let Φ := centerRowResultantFamily e i F d
  have hδL (j) : (map φ F).IsWeightedHomogeneous (chowRowWeight j) d :=
    (isWeightedHomogeneous_map_iff φ.injective _ _ _).mpr (hδ j)
  refine ⟨F,s,e,Φ,hF,⟨hFL,hδL,hzero⟩,
    centerRowResultantFamily_homogeneous e i F d hd hFhom,
    centerRowResultantFamily_totalDegree_le e i F d hd hFhom,?_⟩
  intro A
  exact (centerRowResultantFamily_nonvanishing_iff_extension φ e i F d A).trans
    (chowRowResultant_ne_zero_iff_irreducible JL hJL hJLdim
      (centerMinorProjectionMatrix A e) (map φ F) hzero i d hd (hδL i))

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
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let φ := algebraMap K L
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := L) J hJ
  have hJLdimdeg : HasProjectiveDimensionDegree JL m d :=
    hasProjectiveDimensionDegree_scalar_extension hdimdeg
  obtain ⟨F,s,e,Φ,_,hFL,hhom,hdeg,hdet⟩ :=
    exists_center_resultant_forms (L := L) J hJ d hdimdeg hr
  refine ⟨Φ,hhom,hdeg,?_⟩
  intro A hA
  rw [← projectionImageField_centerMinorProjectionMatrix _ A e]
  let M := centerMinorProjectionMatrix A e
  let R := chowLinearSubstitution M (map φ F)
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span L (Set.range A.row) := by
    have hh := chowLinearSubstitution_ne_zero_iff_center_disjoint JL hJL hJLdimdeg.natDegree_eq M
      (map φ F) hFL.eval_eq_zero_iff
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
    chow_restriction_irreducible_iff_birational_over_closed_field JL hJL d hJLdimdeg
      (map φ F) hFL M (centerMinorProjectionMatrix_disjoint JL A hA e hc)
  constructor
  · intro hg
    have hir := (hdet A).mp hg
    have hc := hcenteriff.mp hir.ne_zero
    exact ⟨hc,(hbir hc).mp hir⟩
  · rintro ⟨hc,hf⟩
    exact (hdet A).mpr ((hbir hc).mpr hf)

end
end CCDN
