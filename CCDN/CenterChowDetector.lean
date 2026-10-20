module

public import CCDN.CenterNoetherForms
public import CCDN.CenterChowCriterion

/-! A finite detector on actual Plücker coordinates, constructed from the
source variety. It detects nonzero irreducible Chow restrictions, forces
center disjointness, and compares actual source and image Chow degrees.
Identifying these degrees with Hilbert multiplicities is a separate bridge. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- The entire polynomial family is chosen before the center. No source or
image equation, chart, matrix witness, or generic-center premise is supplied.
For D at least two the homogeneous detector degree is exactly D(D^2-1). -/
theorem exists_geometric_center_chow_detector
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    (hJ : ∀ f ∈ J, ∀ M, homogeneousComponent M f ∈ J)
    (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hr : r + 2 ≤ n + 2) :
    ∃ (F : MvPolynomial (Fin (m + 1) × Fin (n + 2)) K)
      (δ : Fin (m + 1) → ℕ) (s : ℕ)
      (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      Irreducible F ∧
      (∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i)) ∧
      (∀ U, eval U F = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1) J) ∧
      (∀ g ∈ Φ, g.IsHomogeneous (F.totalDegree * max 1 (F.totalDegree ^ 2 - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ F.totalDegree * max 1 (F.totalDegree ^ 2 - 1)) ∧
      ∀ A : Matrix (Fin r) (Fin (n + 2)) K, LinearIndependent K A.row →
        let good := ∃ g ∈ Φ,
          eval (fun c : Fin r ↪ Fin (n + 2) => (A.submatrix id c).det) g ≠ 0
        (good ↔ Irreducible (chowLinearSubstitution (centerMinorProjectionMatrix A e) F)) ∧
        (good → ∀ p ∈ projectiveIdealZeroLocus J,
          p.rep ∉ Submodule.span K (Set.range A.row)) ∧
        ((∀ p ∈ projectiveIdealZeroLocus J,
          p.rep ∉ Submodule.span K (Set.range A.row)) →
          ∃ G : MvPolynomial (Fin (m + 1) × Fin (s + 2)) K,
            Irreducible G ∧
            (∀ U, eval U G = 0 ↔ U ∈ projectiveChowIncidenceLocus (m + 1)
              (chowProjectionImageIdeal J (centerMinorProjectionMatrix A e))) ∧
            (good ↔ F.totalDegree = G.totalDegree)) := by
  classical
  obtain ⟨F, δ, s, e, hF, hδ, hFzero, _, hcenter⟩ :=
    exists_center_chow_restriction J hJ hdim hr
  have hFhom : F.IsHomogeneous F.totalDegree := by
    have hh := chow_rows_homogeneous_total_degree F δ hδ
    rw [hh.totalDegree hF.ne_zero]
    exact hh
  have hD := mv_totalDegree_pos_of_nonzero_nonunit F hF.ne_zero hF.not_isUnit
  obtain ⟨Φ, hΦhom, hΦdegree, hΦ⟩ := exists_center_noether_forms e F hD hFhom
  refine ⟨F, δ, s, e, Φ, hF, hδ, hFzero, hΦhom, hΦdegree, ?_⟩
  intro A hA
  dsimp only
  have hdet := (hΦ A).trans (irreducible_map_algebraicClosure_iff_of_isAlgClosed _)
  obtain ⟨hne, himage⟩ := hcenter A hA
  rw [universalCenterChowMap_specialize] at hne himage
  refine ⟨hdet, fun hg => hne.mp (hdet.mp hg).ne_zero, ?_⟩
  intro hdisjoint
  obtain ⟨G, _, _, _, hG, _, _, _, hGzero, _, _, hdegree⟩ := himage hdisjoint
  exact ⟨G, hG, hGzero, hdet.trans hdegree⟩

end
end CCDN
