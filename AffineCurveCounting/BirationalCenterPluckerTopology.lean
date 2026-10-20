module

public import AffineCurveCounting.CenterPluckerZariski
public import AffineCurveCounting.BirationalCenterSubspace

/-! Actual geometrically disjoint birational centers form a dense open set
for the Zariski topology induced by their projective maximal minors. This
uses the constructed homogeneous detector and the actual rational witness;
neither a detector nor a witness is a premise of the final theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology projectivePointZariskiTopology
  centerSubspacePluckerZariskiTopology

theorem birationalCenterSubspaceLocus_plucker_isOpen
    {K : Type*} [Field K] [CharZero K] {n m r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2)
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2))) :
    IsOpen (birationalCenterSubspaceLocus J e) := by
  obtain ⟨t, e', Φ, hhom, _, hΦ⟩ := exists_birational_center_detector J hJ d hdim hdegree hr
  have he : birationalCenterSubspaceLocus J e =
      ⋃ g ∈ Φ, centerPluckerPrincipalOpen g := by
    ext W
    obtain ⟨x, rfl⟩ := centerMatrixSpan_surjective W
    have hg (g) (hg : g ∈ Φ) : centerMatrixSpan x ∈ centerPluckerPrincipalOpen g ↔
        eval x.val (centerMinorPolynomial g) ≠ 0 := by
      change x ∈ centerMatrixSpan ⁻¹' centerPluckerPrincipalOpen g ↔ _
      rw [centerMatrixSpan_preimage_pluckerPrincipalOpen g (hhom g hg)]
      rfl
    change x ∈ centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J e ↔ _
    rw [birationalCenterSubspaceLocus_preimage]
    simp only [Set.mem_iUnion]
    have hactual : x ∈ birationalMatrixCenterLocus J e ↔
        ∃ g ∈ Φ, eval x.val (centerMinorPolynomial g) ≠ 0 := by
      change IsBirationalMatrixCenter J e (Matrix.of fun i j => x.val (i,j)) ↔ _
      apply (isBirationalMatrixCenter_iff_enumeration J e e'
        (Matrix.of fun i j => x.val (i,j)) x.property).trans
      simpa only [eval_centerMinorPolynomial, IsBirationalMatrixCenter] using
        (hΦ (Matrix.of fun i j => x.val (i,j)) x.property).symm
    rw [hactual]
    constructor
    · rintro ⟨g, hg', hv⟩
      exact ⟨g, hg', (hg g hg').mpr hv⟩
    · rintro ⟨g, hg', hv⟩
      exact ⟨g, hg', (hg g hg').mp hv⟩
  rw [he]
  exact isOpen_iUnion (fun g => isOpen_iUnion (fun hg =>
    centerPluckerPrincipalOpen_isOpen g (hhom g hg)))

theorem birationalCenterSubspaceLocus_plucker_dense_open
    {n m s : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : ∀ f ∈ J, ∀ N, homogeneousComponent N f ∈ J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (birationalCenterSubspaceLocus J e) ∧ IsOpen (birationalCenterSubspaceLocus J e) :=
  ⟨center_subspace_image_plucker_dense _
      (birationalMatrixCenterLocus_dense hmn J hJ d hdim hdegree e),
    birationalCenterSubspaceLocus_plucker_isOpen J hJ d hdim hdegree (by omega) e⟩

end
end AffineCurveCounting
