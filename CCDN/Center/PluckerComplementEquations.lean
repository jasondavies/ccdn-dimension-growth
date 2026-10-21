/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.BirationalCenterExtensionWitness
public import CCDN.Center.ZeroColumnCenterSubspace
public import CCDN.Center.CenterDetectorBounds
public import CCDN.Algebra.PolynomialPredicates
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

lemma birationalCenterSubspaceLocus_congr
    {K : Type*} [Field K] {n r : ℕ}
    {J J' : Ideal (MvPolynomial (Fin (n + 1)) K)} [J.IsPrime] [J'.IsPrime] (h : J = J') :
    birationalCenterSubspaceLocus (r := r) J = birationalCenterSubspaceLocus J' := by
  subst h
  rfl

/-- The good locus has dense intersection with the centers having zero
columns `S`, as soon as one such center lies outside the zero locus. -/
theorem zeroColumnCenterSubspace_familyComplement_dense
    {K L : Type*} [Field K] [Field L] [Infinite L] (φ : K →+* L) {r n D : ℕ}
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K)) (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D)
    (S : Finset (Fin n)) (x : ZeroColumnCenterMatrix L r n S)
    (hx : centerMatrixSpan ⟨x.val, x.property.2⟩ ∈ (centerPluckerFamilyZeroLocus φ Φ)ᶜ) :
    Dense {W : ZeroColumnCenterSubspace L r n S |
      W.val ∈ (centerPluckerFamilyZeroLocus φ Φ)ᶜ} := by
  obtain ⟨g,hg,hv⟩ := (centerMatrixSpan_mem_familyComplement_iff φ Φ hΦ _).mp hx
  let A : Matrix (Fin r) (Fin n) L := Matrix.of fun i j => x.val (i,j)
  have hp : zeroColumnSubstitution S (centerMinorPolynomial (map φ g)) ≠ 0 := by
    intro hz
    have h0 := congrArg (eval x.val) hz
    rw [eval_zeroColumnSubstitution,zeroColumnPoint_fixed S _ x.property.1,map_zero] at h0
    exact hv h0
  have hdense := zeroColumnMatrixSpan_surjective.denseRange.dense_image
    zeroColumnMatrixSpan_continuous
    (zero_column_polynomial_locus_dense_subspace S A x.property.2 x.property.1 _ hp)
  refine hdense.mono ?_
  rintro _ ⟨y,hy,rfl⟩
  exact (centerMatrixSpan_mem_familyComplement_iff φ Φ hΦ _).mpr ⟨g,hg,hy⟩

/-- The ambient case `S = ∅`. -/
theorem centerSubspace_familyComplement_dense
    {K L : Type*} [Field K] [Field L] [Infinite L] (φ : K →+* L) {r n D : ℕ}
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin n) K)) (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D)
    (x : IndependentCenterMatrix L r n)
    (hx : centerMatrixSpan x ∈ (centerPluckerFamilyZeroLocus φ Φ)ᶜ) :
    Dense (centerPluckerFamilyZeroLocus φ Φ)ᶜ := by
  have hd := zeroColumnCenterSubspace_familyComplement_dense φ Φ hΦ ∅
    ⟨x.val,fun _ _ h => absurd h (Finset.notMem_empty _),x.property⟩ hx
  have hsurj : Function.Surjective
      (Subtype.val : ZeroColumnCenterSubspace L r n ∅ → CenterSubspace L r n) :=
    fun W => ⟨⟨W,fun _ _ _ h => absurd h (Finset.notMem_empty _)⟩,rfl⟩
  refine (hsurj.denseRange.dense_image continuous_subtype_val hd).mono ?_
  rintro _ ⟨W,hW,rfl⟩
  exact hW

lemma birationalCenterSubspaceLocus_eq_complement_of_extension_detector
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) {n r D : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) L)) [J.IsPrime]
    (Φ : Finset (MvPolynomial (Fin r ↪ Fin (n + 1)) K))
    (hΦ : ∀ g ∈ Φ, g.IsHomogeneous D)
    (hdet : ∀ (A : Matrix (Fin r) (Fin (n + 1)) L), LinearIndependent L A.row →
      ((∃ g ∈ Φ, eval₂ φ (matrixPluckerCoordinates A) g ≠ 0) ↔ IsBirationalMatrixCenter J A)) :
    birationalCenterSubspaceLocus J = (centerPluckerFamilyZeroLocus φ Φ)ᶜ := by
  ext W
  obtain ⟨x,rfl⟩ := centerMatrixSpan_surjective W
  change x ∈ centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus J ↔ _
  rw [birationalCenterSubspaceLocus_preimage,centerMatrixSpan_mem_familyComplement_iff φ Φ hΦ]
  change IsBirationalMatrixCenter J (Matrix.of fun i j => x.val (i,j)) ↔ _
  refine (hdet (Matrix.of fun i j => x.val (i,j)) x.property).symm.trans ?_
  simp only [eval_centerMinorPolynomial,eval_map]

theorem exists_birational_center_plucker_equations
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
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      birationalCenterSubspaceLocus (J.map (map (algebraMap K L))) =
        (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ := by
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  obtain ⟨Φ,hhom,hdeg,hdet⟩ :=
    exists_extended_birational_center_detector (L := L) J hJ d ⟨hdim, hdegree⟩ hr
  refine ⟨Φ,hhom,hdeg,?_,?_,birationalCenterSubspaceLocus_eq_complement_of_extension_detector
    (algebraMap K L) (J.map (map (algebraMap K L))) Φ hhom hdet⟩
  · intro hm g hg
    exact (hdeg g hg).trans_lt (center_detector_degree_lt_square hm
      (hilbert_multiplicity_pos_of_prime J hdegree))
  · intro hm
    have hd : d = 1 :=
      (geometric_projective_multiplicity_boundary J hJ ⟨hdim, hdegree⟩).resolve_left (by omega)
    refine ⟨hd,fun g hg => ?_⟩
    simpa only [hm,hd,Nat.zero_add,mul_one,Nat.reduceSub] using hdeg g hg

/-- The printed positive-dimensional degree bound and the degree-one
boundary hold on the geometric subspaces over every extension L. -/
theorem exists_dense_open_projective_center_plucker_equations
    {L : Type*} [Field L] [Algebra ℚ L] {n m : ℕ}
    (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    letI : (J.map (map (algebraMap ℚ L))).IsPrime :=
      prime_ideal_scalar_extension_of_algebraicClosure J
    ∃ Φ : Finset (MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) ℚ),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      birationalCenterSubspaceLocus (J.map (map (algebraMap ℚ L))) =
        (centerPluckerFamilyZeroLocus (algebraMap ℚ L) Φ)ᶜ ∧
      Dense (birationalCenterSubspaceLocus (r := n + 1 - m - 1) (J.map (map (algebraMap ℚ L)))) ∧
      IsOpen (birationalCenterSubspaceLocus (r := n + 1 - m - 1)
        (J.map (map (algebraMap ℚ L)))) := by
  have hJL : (J.map (map (algebraMap ℚ L))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨Φ,hhom,hdeg,hstrict,hboundary,he⟩ :=
    exists_birational_center_plucker_equations (L := L) (r := n + 1 - m - 1)
      J hJ d hdimdeg (by omega)
  obtain ⟨A,hA,hgood⟩ := exists_birational_center_matrix_over_extension
    (L := L) hmn J hJ d hdimdeg
  let x : IndependentCenterMatrix L (n + 1 - m - 1) (n + 2) := ⟨fun q => A q.1 q.2,hA⟩
  have hx : centerMatrixSpan x ∈ (centerPluckerFamilyZeroLocus (algebraMap ℚ L) Φ)ᶜ := by
    rw [← he]
    exact ⟨x,hgood,rfl⟩
  refine ⟨Φ,hhom,hdeg,hstrict,hboundary,he,?_,?_⟩
  · rw [he]
    exact centerSubspace_familyComplement_dense _ Φ hhom _ hx
  · rw [he]
    exact centerPluckerFamilyZeroLocus_complement_isOpen _ Φ hhom

/-- The good-center subspaces of a rational geometric projective variety
form a dense open set in the Plücker topology. -/
theorem birationalCenterSubspaceLocus_plucker_dense_open
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    Dense (birationalCenterSubspaceLocus (r := n + 1 - m - 1) J) ∧
      IsOpen (birationalCenterSubspaceLocus (r := n + 1 - m - 1) J) := by
  have : (J.map (map (algebraMap ℚ ℚ))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure J
  obtain ⟨_,_,_,_,_,_,hdense,hopen⟩ :=
    exists_dense_open_projective_center_plucker_equations (L := ℚ) hmn J hJ d hdimdeg
  rw [birationalCenterSubspaceLocus_congr (ideal_map_algebraMap_self J)] at hdense hopen
  exact ⟨hdense,hopen⟩

end
end CCDN
