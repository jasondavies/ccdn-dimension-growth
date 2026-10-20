module

public import CCDN.BirationalCenterExtensionWitness
public import CCDN.CenterPluckerZariski
public import CCDN.BirationalCenterSubspace
public import CCDN.SharpCenterBounds
public import CCDN.PolynomialPredicates

/-! Sharp homogeneous equations for the complement of the good-center
locus in Pluecker coordinates, including coefficient-field extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology projectivePointZariskiTopology
  centerSubspacePluckerZariskiTopology

/-- Common zero set on subspaces of equations defined over K and
evaluated at their projective Pluecker representatives over L. -/
def centerPluckerFamilyZeroLocus
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n : ℕ}
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K)) : Set (CenterSubspace L r n) :=
  {W | ∀ g ∈ Φ, eval₂ φ (centerSubspacePlucker W).rep g = 0}

lemma centerPluckerFamilyZeroLocus_complement_isOpen
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n D : ℕ}
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K))
    (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D) :
    IsOpen (centerPluckerFamilyZeroLocus φ Φ)ᶜ := by
  have he : (centerPluckerFamilyZeroLocus φ Φ)ᶜ =
      ⋃ g ∈ Φ, centerPluckerPrincipalOpen (map φ g) := by
    ext W
    simp [centerPluckerFamilyZeroLocus,centerPluckerPrincipalOpen,
      projectiveHomogeneousPrincipalOpen,eval_map]
  rw [he]
  exact isOpen_iUnion (fun g => isOpen_iUnion (fun hg =>
    centerPluckerPrincipalOpen_isOpen (map φ g) ((hΦ g hg).map φ)))

lemma homogeneous_eval₂_centerMatrixSpan
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n D : ℕ}
    (g : MvPolynomial (Fin r ↪ Fin n) K) (hg : g.IsHomogeneous D)
    (x : IndependentCenterMatrix L r n) :
    eval₂ φ (centerSubspacePlucker (centerMatrixSpan x)).rep g = 0 ↔
      eval₂ φ (matrixPluckerCoordinates (Matrix.of fun i j => x.val (i,j))) g = 0 := by
  rw [centerSubspacePlucker_matrixSpan,eval₂_eq_eval_map,eval₂_eq_eval_map]
  exact homogeneous_eval_independentCenterPlucker (map φ g) (hg.map φ) x

lemma centerMatrixSpan_mem_familyComplement_iff
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {r n D : ℕ}
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K)) (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D)
    (x : IndependentCenterMatrix L r n) :
    centerMatrixSpan x ∈ (centerPluckerFamilyZeroLocus φ Φ)ᶜ ↔
      ∃ g ∈ Φ, eval x.val (centerMinorPolynomial (map φ g)) ≠ 0 := by
  change (¬ ∀ g ∈ Φ, eval₂ φ (centerSubspacePlucker (centerMatrixSpan x)).rep g = 0) ↔ _
  simp only [not_forall,eval_centerMinorPolynomial,eval_map]
  constructor
  · rintro ⟨g,hg,hv⟩
    exact ⟨g,hg,fun hz => hv ((homogeneous_eval₂_centerMatrixSpan φ g (hΦ g hg) x).mpr hz)⟩
  · rintro ⟨g,hg,hv⟩
    exact ⟨g,hg,fun hz => hv ((homogeneous_eval₂_centerMatrixSpan φ g (hΦ g hg) x).mp hz)⟩

lemma ideal_map_algebraMap_self {K σ : Type*} [Field K] (J : Ideal (MvPolynomial σ K)) :
    J.map (map (algebraMap K K)) = J := by
  have h : (map (algebraMap K K) : MvPolynomial σ K →+* MvPolynomial σ K) = RingHom.id _ := by
    ext <;> simp
  rw [h,Ideal.map_id]

lemma birationalCenterSubspaceLocus_congr
    {K : Type*} [Field K] {n r s t : ℕ}
    (J J' : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] [J'.IsPrime]
    (h : J = J') (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (e' : Fin (t + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    birationalCenterSubspaceLocus J e = birationalCenterSubspaceLocus J' e' := by
  subst J'
  ext W
  obtain ⟨x,rfl⟩ := centerMatrixSpan_surjective W
  change x ∈ centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J e ↔
    x ∈ centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J e'
  rw [birationalCenterSubspaceLocus_preimage,birationalCenterSubspaceLocus_preimage]
  exact isBirationalMatrixCenter_iff_enumeration J e e' _ x.property

lemma birationalCenterSubspaceLocus_eq_complement_of_extension_detector
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {n r s D : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) L)) [J.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1)))
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 1)) K))
    (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D)
    (hdet : ∀ (A : Matrix (Fin r) (Fin (n + 1)) L), LinearIndependent L A.row →
      ((∃ g ∈ Φ, eval₂ φ (matrixPluckerCoordinates A) g ≠ 0) ↔ IsBirationalMatrixCenter J e A)) :
    birationalCenterSubspaceLocus J e = (centerPluckerFamilyZeroLocus φ Φ)ᶜ := by
  ext W
  obtain ⟨x,rfl⟩ := centerMatrixSpan_surjective W
  change x ∈ centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J e ↔ _
  rw [birationalCenterSubspaceLocus_preimage]
  change IsBirationalMatrixCenter J e (Matrix.of fun i j => x.val (i,j)) ↔ _
  refine (hdet (Matrix.of fun i j => x.val (i,j)) x.property).symm.trans ?_
  change (∃ g ∈ Φ, eval₂ φ (matrixPluckerCoordinates (Matrix.of fun i j => x.val (i,j))) g ≠ 0) ↔
    ¬ ∀ g ∈ Φ, eval₂ φ (centerSubspacePlucker (centerMatrixSpan x)).rep g = 0
  simp only [not_forall]
  constructor
  · rintro ⟨g,hg,hv⟩
    exact ⟨g,hg,fun hz => hv ((homogeneous_eval₂_centerMatrixSpan φ g (hΦ g hg) x).mp hz)⟩
  · rintro ⟨g,hg,hv⟩
    exact ⟨g,hg,fun hz => hv ((homogeneous_eval₂_centerMatrixSpan φ g (hΦ g hg) x).mpr hz)⟩

theorem exists_sharp_birational_center_plucker_equations
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    [(J.map (map (algebraMap K L))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2) :
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 2)) K)),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      birationalCenterSubspaceLocus (J.map (map (algebraMap K L))) e =
        (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ ∧
      IsOpen (birationalCenterSubspaceLocus (J.map (map (algebraMap K L))) e) := by
  obtain ⟨s,e,Φ,hhom,hdeg,hdet⟩ :=
    exists_sharp_extended_birational_center_detector (L := L) J hJ d hdim hdegree hr
  have he := birationalCenterSubspaceLocus_eq_complement_of_extension_detector
    (algebraMap K L) (J.map (map (algebraMap K L))) e Φ hhom hdet
  refine ⟨s,e,Φ,hhom,hdeg,?_,?_,he,?_⟩
  · intro hm g hg
    exact (hdeg g hg).trans_lt (sharp_center_detector_degree_lt_square hm
      (hilbert_multiplicity_pos_of_prime J hdegree))
  · intro hm
    have hd : d = 1 := (geometric_projective_multiplicity_boundary J hJ hdim hdegree).resolve_left
      (by omega)
    refine ⟨hd,fun g hg => ?_⟩
    simpa only [hm,hd,Nat.zero_add,mul_one,Nat.reduceSub] using hdeg g hg
  · rw [he]
    exact centerPluckerFamilyZeroLocus_complement_isOpen _ Φ hhom

/-- The printed positive-dimensional degree bound and the degree-one
boundary hold on the geometric subspaces over every extension L. -/
theorem exists_dense_open_sharp_projective_center_plucker_equations
    {L : Type*} [Field L] [Algebra ℚ L] {n m : ℕ}
    (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial) :
    letI : (J.map (map (algebraMap ℚ L))).IsPrime :=
      prime_ideal_scalar_extension_of_algebraicClosure J
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) ℚ)),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      birationalCenterSubspaceLocus (J.map (map (algebraMap ℚ L))) e =
        (centerPluckerFamilyZeroLocus (algebraMap ℚ L) Φ)ᶜ ∧
      Dense (birationalCenterSubspaceLocus (J.map (map (algebraMap ℚ L))) e) ∧
      IsOpen (birationalCenterSubspaceLocus (J.map (map (algebraMap ℚ L))) e) := by
  have hJL : (J.map (map (algebraMap ℚ L))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨s,e,Φ,hhom,hdeg,hstrict,hboundary,he,hopen⟩ :=
    exists_sharp_birational_center_plucker_equations (L := L) (r := n + 1 - m - 1)
      J hJ d hdim hdegree (by omega)
  obtain ⟨A,hA,hgood⟩ := exists_birational_center_matrix_over_extension
    (L := L) hmn J hJ d hdim hdegree e
  let x : IndependentCenterMatrix L (n + 1 - m - 1) (n + 2) :=
    ⟨fun q => A q.1 q.2,hA⟩
  have hx : centerMatrixSpan x ∈ birationalCenterSubspaceLocus (J.map (map (algebraMap ℚ L))) e :=
    ⟨x,hgood,rfl⟩
  rw [he] at hx
  obtain ⟨g,hg,hv⟩ := (centerMatrixSpan_mem_familyComplement_iff _ Φ hhom x).mp hx
  have hdense := centerPluckerPrincipalOpen_dense (map (algebraMap ℚ L) g)
    ((hhom g hg).map _) x hv
  refine ⟨s,e,Φ,hhom,hdeg,hstrict,hboundary,he,hdense.mono ?_,hopen⟩
  intro W hW
  rw [he]
  intro hz
  change eval (centerSubspacePlucker W).rep (map (algebraMap ℚ L) g) ≠ 0 at hW
  rw [eval_map] at hW
  exact hW (hz g hg)

/-- The good-center subspaces of a rational geometric projective variety
form a dense open set in the Plücker topology. -/
theorem birationalCenterSubspaceLocus_plucker_dense_open
    {n m s : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (birationalCenterSubspaceLocus J e) ∧ IsOpen (birationalCenterSubspaceLocus J e) := by
  have : (J.map (map (algebraMap ℚ ℚ))).IsPrime := prime_ideal_scalar_extension_of_algebraicClosure J
  obtain ⟨t,e',_,_,_,_,_,_,hdense,hopen⟩ :=
    exists_dense_open_sharp_projective_center_plucker_equations (L := ℚ) hmn J hJ d hdim hdegree
  rw [birationalCenterSubspaceLocus_congr _ J (ideal_map_algebraMap_self J) e' e] at hdense hopen
  exact ⟨hdense,hopen⟩

end
end CCDN
