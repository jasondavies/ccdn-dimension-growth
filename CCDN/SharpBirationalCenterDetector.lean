module

public import CCDN.SharpCenterResultantDetector
public import CCDN.PolynomialPredicates

/-! Sharp resultant detectors for base-field centers, with geometric
disjointness and the base-field birationality conclusion. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma eval₂_center_minor_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) K) (g : MvPolynomial (Fin r ↪ Fin n) K) :
    eval₂ φ (fun c : Fin r ↪ Fin n => ((A.map φ).submatrix id c).det) g =
      φ (eval (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) g) := by
  have hm (c : Fin r ↪ Fin n) : ((A.map φ).submatrix id c).det = φ ((A.submatrix id c).det) :=
    (φ.map_det (A.submatrix id c)).symm
  simp_rw [hm]
  exact (eval₂_comp_left φ (RingHom.id K)
    (fun c : Fin r ↪ Fin n => (A.submatrix id c).det) g).symm

/-- The nonvanishing locus is exactly the set of geometrically disjoint
centers whose projection is birational. No Chow equation, image
multiplicity, or witness center is supplied. -/
theorem exists_sharp_birational_center_detector
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
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
  obtain ⟨F,s,e,Φ,_,hFL,hδ,hFzero,hΦhom,hΦdegree,hΦ⟩ :=
    exists_sharp_center_resultant_forms (L := AlgebraicClosure K) J hJ d hdim hdegree hr
  refine ⟨s,e,Φ,hΦhom,hΦdegree,?_⟩
  intro A hA
  let AL := A.map φ
  let M := centerMinorProjectionMatrix AL e
  let R := chowLinearSubstitution M (map φ F)
  have hAL : LinearIndependent (AlgebraicClosure K) AL.row :=
    linearIndependent_matrix_rows_map φ A hA
  have hdet := hΦ AL
  simp only [AL,φ,eval₂_center_minor_map,
    map_ne_zero_iff (algebraMap K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective] at hdet
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
