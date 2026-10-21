module

public import CCDN.SharpPluckerComplementEquations

/-! Sharp equations for the complement of the good-center locus at
infinity of an affine source, including geometric coefficient extensions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology projectivePointZariskiTopology
  centerSubspacePluckerZariskiTopology

theorem exists_dense_open_sharp_fixed_center_plucker_equations
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    letI : (I.map (map (algebraMap K L))).IsPrime :=
      prime_ideal_scalar_extension_of_algebraicClosure I
    ∃ Φ : Finset (MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) K),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      fixedCoordinateBirationalSubspaceLocus (I.map (map (algebraMap K L))) =
        (Subtype.val ⁻¹' centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ ∧
      Dense (fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1)
        (I.map (map (algebraMap K L)))) ∧
      IsOpen (fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1)
        (I.map (map (algebraMap K L)))) := by
  have hIL : (I.map (map (algebraMap K L))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure I
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let IL := I.map (map (algebraMap K L))
  have hclgeo := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure K) I
  have hclL := projectiveClosureIdeal_geometrically_prime (L := L) I
  obtain ⟨hcdim,hcdegree⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  obtain ⟨Φ,hhom,hdeg,hstrict,hboundary,he⟩ :=
    exists_sharp_birational_center_plucker_equations (L := L) (r := n + 1 - m - 1)
      (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) d hcdim hcdegree (by omega)
  have heq : fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1) IL =
      Subtype.val ⁻¹' (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ := by
    change Subtype.val ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal IL) = _
    rw [birationalCenterSubspaceLocus_congr
      (projectiveClosureIdeal_scalar_extension (L := L) I).symm, he]
  obtain ⟨A,hA,hA0,hgood⟩ :=
    exists_fixed_coordinate_birational_center_matrix_over_extension (L := L) I hmn d hdim hdegree
  let x : FixedCoordinateCenterMatrix L (n + 1 - m - 1) (n + 1) :=
    ⟨fun q => A q.1 q.2,
      fun i j hj => by simpa only [Finset.mem_singleton.mp hj] using hA0 i, hA⟩
  have hx : centerMatrixSpan ⟨x.val, x.property.2⟩ ∈
      (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ := by
    rw [← he]
    exact ⟨⟨x.val, x.property.2⟩,hgood,rfl⟩
  refine ⟨Φ,hhom,hdeg,hstrict,hboundary,heq,?_,?_⟩
  · rw [heq]
    exact zeroColumnCenterSubspace_familyComplement_dense _ Φ hhom {0} x hx
  · rw [heq]
    exact (centerPluckerFamilyZeroLocus_complement_isOpen _ Φ hhom).preimage continuous_subtype_val

/-- The good centers in X0=0 form a dense open set of the subspace of such
centers, in the Plücker topology. -/
theorem fixedCoordinateBirationalSubspaceLocus_plucker_dense_open
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    Dense (fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1) I) ∧
      IsOpen (fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1) I) := by
  have : (I.map (map (algebraMap K K))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure I
  obtain ⟨_,_,_,_,_,_,hdense,hopen⟩ :=
    exists_dense_open_sharp_fixed_center_plucker_equations (L := K) I hmn d hdim hdegree
  have : (projectiveClosureIdeal (I.map (map (algebraMap K K)))).IsPrime :=
    projectiveClosureIdeal_isPrime _
  have he : fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1)
      (I.map (map (algebraMap K K))) = fixedCoordinateBirationalSubspaceLocus I := by
    change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
    rw [birationalCenterSubspaceLocus_congr
      (congrArg projectiveClosureIdeal (ideal_map_algebraMap_self I))]
  rw [he] at hdense hopen
  exact ⟨hdense,hopen⟩

end
end CCDN
