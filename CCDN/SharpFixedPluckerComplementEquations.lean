module

public import CCDN.SharpPluckerComplementEquations
public import CCDN.FixedCoordinatePluckerTopology

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
    ∃ (s : ℕ) (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2)))
      (Φ : Finset (MvPolynomial (Fin (n + 1 - m - 1) ↪ Fin (n + 2)) K)),
      (∀ g ∈ Φ, g.IsHomogeneous (((m + 1) * d) * (2 * d - 1))) ∧
      (∀ g ∈ Φ, g.totalDegree ≤ ((m + 1) * d) * (2 * d - 1)) ∧
      (1 ≤ m → ∀ g ∈ Φ, g.totalDegree < ((m + 1) * d) ^ 2) ∧
      (m = 0 → d = 1 ∧ ∀ g ∈ Φ, g.totalDegree ≤ 1) ∧
      fixedCoordinateBirationalSubspaceLocus (I.map (map (algebraMap K L))) e =
        (Subtype.val ⁻¹' centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ ∧
      Dense (fixedCoordinateBirationalSubspaceLocus (I.map (map (algebraMap K L))) e) ∧
      IsOpen (fixedCoordinateBirationalSubspaceLocus (I.map (map (algebraMap K L))) e) := by
  have hIL : (I.map (map (algebraMap K L))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure I
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let IL := I.map (map (algebraMap K L))
  have hIE : (I.map (map (algebraMap K (AlgebraicClosure L)))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure I
  have hILE : (IL.map (map (algebraMap L (AlgebraicClosure L)))).IsPrime := by
    dsimp only [IL]
    rw [ideal_scalar_extension_tower]
    exact hIE
  have hclgeo := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure K) I
  have hclL := projectiveClosureIdeal_geometrically_prime (L := L) I
  obtain ⟨hcdim,hcdegree⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  obtain ⟨s,e,Φ,hhom,hdeg,hstrict,hboundary,he,_⟩ :=
    exists_sharp_birational_center_plucker_equations (L := L) (r := n + 1 - m - 1)
      (projectiveClosureIdeal I)
      (projectiveClosureIdeal_homogeneous I) d hcdim hcdegree (by omega)
  have he' : birationalCenterSubspaceLocus (projectiveClosureIdeal IL) e =
      (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ :=
    (birationalCenterSubspaceLocus_congr _ _
      (projectiveClosureIdeal_scalar_extension (L := L) I) e e).symm.trans he
  have heq : fixedCoordinateBirationalSubspaceLocus IL e =
      Subtype.val ⁻¹' (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ := by
    change Subtype.val ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal IL) e = _
    rw [he']
  obtain ⟨A,hA,hA0,hgood⟩ :=
    exists_fixed_coordinate_birational_center_matrix_over_extension (L := L) I hmn d hdim hdegree e
  have hAz : ∀ i j, j ∈ ({0} : Finset (Fin (n + 2))) → A i j = 0 := by
    intro i j hj
    simpa only [Finset.mem_singleton.mp hj] using hA0 i
  let x : IndependentCenterMatrix L (n + 1 - m - 1) (n + 2) := ⟨fun q => A q.1 q.2,hA⟩
  have hx : centerMatrixSpan x ∈ (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ := by
    rw [← he]
    exact ⟨x,hgood,rfl⟩
  obtain ⟨g,hg,hv⟩ := (centerMatrixSpan_mem_familyComplement_iff _ Φ hhom x).mp hx
  have hp : zeroColumnSubstitution {0} (centerMinorPolynomial (map (algebraMap K L) g)) ≠ 0 := by
    intro hz
    have h0 := congrArg (eval (fun q => A q.1 q.2)) hz
    rw [eval_zeroColumnSubstitution,zeroColumnPoint_fixed {0} _ hAz,map_zero] at h0
    exact hv h0
  have hdense := fixedCoordinateMatrixSpan_surjective.denseRange.dense_image
    fixedCoordinateMatrixSpan_continuous (zero_column_polynomial_locus_dense_subspace {0} A hA hAz _ hp)
  refine ⟨s,e,Φ,hhom,hdeg,hstrict,hboundary,heq,hdense.mono ?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    rw [heq]
    exact (centerMatrixSpan_mem_familyComplement_iff _ Φ hhom ⟨y.val,y.property.2⟩).mpr ⟨g,hg,hy⟩
  · rw [heq]
    exact (centerPluckerFamilyZeroLocus_complement_isOpen _ Φ hhom).preimage continuous_subtype_val

/-- The good centers in X0=0 form a dense open set of the subspace of such
centers, in the Plücker topology. -/
theorem fixedCoordinateBirationalSubspaceLocus_plucker_dense_open
    {K : Type*} [Field K] [CharZero K] {n m s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (fixedCoordinateBirationalSubspaceLocus I e) ∧
      IsOpen (fixedCoordinateBirationalSubspaceLocus I e) := by
  have : (I.map (map (algebraMap K K))).IsPrime := prime_ideal_scalar_extension_of_algebraicClosure I
  obtain ⟨t,e',_,_,_,_,_,_,hdense,hopen⟩ :=
    exists_dense_open_sharp_fixed_center_plucker_equations (L := K) I hmn d hdim hdegree
  have : (projectiveClosureIdeal (I.map (map (algebraMap K K)))).IsPrime :=
    projectiveClosureIdeal_isPrime _
  have he : fixedCoordinateBirationalSubspaceLocus (I.map (map (algebraMap K K))) e' =
      fixedCoordinateBirationalSubspaceLocus I e := by
    change Subtype.val ⁻¹' _ = Subtype.val ⁻¹' _
    rw [birationalCenterSubspaceLocus_congr _ _
      (congrArg projectiveClosureIdeal (ideal_map_algebraMap_self I)) e' e]
  rw [he] at hdense hopen
  exact ⟨hdense,hopen⟩

end
end CCDN
