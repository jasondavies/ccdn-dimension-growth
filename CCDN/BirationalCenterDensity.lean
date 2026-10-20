module

public import CCDN.BirationalCenterLocus
public import CCDN.PolynomialPredicates

/-! The complete geometrically disjoint birational-center locus is Zariski
open. For a rational geometric projective variety in the stated ambient
range it is also dense, using a constructed center, not a supplied witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

theorem birationalMatrixCenterLocus_isOpen
    {K : Type*} [Field K] [CharZero K] {n m r s : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2)
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2))) :
    IsOpen (birationalMatrixCenterLocus J e) := by
  classical
  obtain ⟨t,e',Φ,_,_,hΦ⟩ := exists_birational_center_detector J hJ d hdim hdegree hr
  have heq : birationalMatrixCenterLocus J e =
      ⋃ g : {g // g ∈ Φ},
        {x : IndependentCenterMatrix K r (n + 2) |
          eval x.val (centerMinorPolynomial g.val) ≠ 0} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    change IsBirationalMatrixCenter J e (Matrix.of fun i j => x.val (i,j)) ↔ _
    refine (isBirationalMatrixCenter_iff_enumeration J e e'
      (Matrix.of fun i j => x.val (i,j)) x.property).trans ?_
    change _ ↔ ∃ g : {g // g ∈ Φ}, _
    constructor
    · intro hx
      obtain ⟨g,hg,hv⟩ := (hΦ _ x.property).mpr hx
      exact ⟨⟨g,hg⟩,by rwa [eval_centerMinorPolynomial]⟩
    · rintro ⟨g,hg⟩
      apply (hΦ _ x.property).mp
      exact ⟨g.val,g.property,by rwa [eval_centerMinorPolynomial] at hg⟩
  rw [heq]
  exact isOpen_iUnion (fun g =>
    full_row_rank_polynomial_locus_isOpen_subspace (centerMinorPolynomial g.val))

theorem birationalMatrixCenterLocus_dense
    {n m s : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (birationalMatrixCenterLocus J e) := by
  obtain ⟨t,e',G,A,_,_,hA,hG,hgood⟩ :=
    exists_nonzero_birational_center_detector hmn J hJ d hdim hdegree
  obtain ⟨c,hc,_⟩ := exists_nonzero_minor_of_independent_rows A hA
  have hp : centerMinorPolynomial G ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun q => A q.1 q.2)) hz
    rw [eval_centerMinorPolynomial,map_zero] at he
    exact hG he
  apply (full_row_rank_polynomial_locus_dense_subspace ⟨c,hc⟩ _ hp).mono
  intro x hx
  change IsBirationalMatrixCenter J e (Matrix.of fun i j => x.val (i,j))
  apply (isBirationalMatrixCenter_iff_enumeration J e e' _ x.property).mpr
  apply hgood _ x.property
  change eval x.val (centerMinorPolynomial G) ≠ 0 at hx
  rwa [eval_centerMinorPolynomial] at hx

/-- Both conclusions concern the entire actual good-center locus. -/
theorem birationalMatrixCenterLocus_dense_open
    {n m s : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (birationalMatrixCenterLocus J e) ∧ IsOpen (birationalMatrixCenterLocus J e) :=
  ⟨birationalMatrixCenterLocus_dense hmn J hJ d hdim hdegree e,
    birationalMatrixCenterLocus_isOpen J hJ d hdim hdegree (by omega) e⟩

end
end CCDN
