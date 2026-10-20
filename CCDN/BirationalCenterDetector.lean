module

public import CCDN.GeometricCenterNoetherForms
public import CCDN.ChowRestrictionBirational
public import CCDN.PolynomialPredicates

/-! Good centers are detected by a finite family of homogeneous
polynomials in maximal minors. The degree comes from the Noether-form
composition, with the degree-one boundary treated by coefficient forms. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- The nonvanishing locus is exactly the set of geometrically disjoint
centers whose projection is birational. -/
theorem exists_birational_center_detector
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * max 1 (((m + 1) * d) ^ 2 - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * max 1 (((m + 1) * d) ^ 2 - 1)) ∧
      ∀ (A : Matrix (Fin r) (Fin (n + 2)) K) (_ : LinearIndependent K A.row),
        (∃ g ∈ Φ, eval (fun c : Fin r ↪ Fin (n + 2) => (A.submatrix id c).det) g ≠ 0) ↔
        (∀ p ∈ projectiveIdealZeroLocus (J.map (map (algebraMap K (AlgebraicClosure K)))),
          p.rep ∉ Submodule.span (AlgebraicClosure K)
            (Set.range (A.map (algebraMap K (AlgebraicClosure K))).row)) ∧
        projectionImageField (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J))
          J (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  let JL := J.map (map φ)
  have hJL := homogeneous_ideal_scalar_extension (L := AlgebraicClosure K) J hJ
  have hJLdim : (filteredHilbertPolynomial JL).natDegree = m + 1 := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  obtain ⟨F, hF, hFL, hδ, hFdegree, hFzero⟩ :=
    exists_geometric_projective_chow_exact_degree (L := AlgebraicClosure K) J hJ d hdim hdegree
  obtain ⟨s, ⟨e⟩⟩ := exists_center_minor_coordinate_enumeration hr
  have hFhom : F.IsHomogeneous F.totalDegree := by
    have hh := chow_rows_homogeneous_total_degree F (fun _ => d) hδ
    rw [hh.totalDegree hF.ne_zero]
    exact hh
  obtain ⟨Φ, hΦhom, hΦdegree, hΦ⟩ := exists_center_noether_forms e F
    (mv_totalDegree_pos_of_nonzero_nonunit F hF.ne_zero hF.not_isUnit) hFhom
  refine ⟨s, e, Φ, ?_, ?_, ?_⟩
  · simpa only [hFdegree] using hΦhom
  · simpa only [hFdegree] using hΦdegree
  intro A hA
  let AL := A.map φ
  let M := centerMinorProjectionMatrix AL e
  let R := chowLinearSubstitution M (map φ F)
  have hAL : LinearIndependent (AlgebraicClosure K) AL.row :=
    linearIndependent_matrix_rows_map φ A hA
  have hdet := hΦ A
  rw [centerChowRestriction_map] at hdet
  have hcenteriff : R ≠ 0 ↔ ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span (AlgebraicClosure K) (Set.range AL.row) := by
    have hh := chowLinearSubstitution_ne_zero_iff_center_disjoint JL hJL hJLdim M
      (map φ F) hFzero
    refine hh.trans ⟨?_, centerMinorProjectionMatrix_disjoint JL AL hAL e⟩
    intro h p hp hspan
    apply h p hp
    change p.rep ∈ M.mulVecLin.ker
    rwa [centerMinorProjectionMatrix_ker AL hAL e]
  have hbir (hc : ∀ p ∈ projectiveIdealZeroLocus JL,
      p.rep ∉ Submodule.span (AlgebraicClosure K) (Set.range AL.row)) :
      Irreducible R ↔ projectionImageField
        (F := FractionRing (MvPolynomial (Fin (n + 2)) K ⧸ J)) J
        (chowProjectionForms (centerMinorProjectionMatrix A e)) = ⊤ := by
    have hdisjoint := centerMinorProjectionMatrix_disjoint JL AL hAL e hc
    have hh := geometric_chow_restriction_irreducible_iff_birational J hJ d hdim hdegree
      F hFL hδ hFzero (centerMinorProjectionMatrix A e)
    rw [centerMinorProjectionMatrix_map] at hh
    exact hh hdisjoint
  constructor
  · intro hg
    have hir := hdet.mp hg
    have hc := hcenteriff.mp hir.ne_zero
    exact ⟨hc, (hbir hc).mp hir⟩
  · rintro ⟨hc, hf⟩
    exact hdet.mpr ((hbir hc).mpr hf)

end
end CCDN
