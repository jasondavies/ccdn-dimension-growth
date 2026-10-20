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

lemma birationalCenterSubspaceLocus_congr
    {K : Type*} [Field K] {n r s : ℕ}
    (J J' : Ideal (MvPolynomial (Fin (n + 1)) K)) [J.IsPrime] [J'.IsPrime]
    (h : J = J') (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    birationalCenterSubspaceLocus J e = birationalCenterSubspaceLocus J' e := by
  subst J'
  rfl

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
  have hILdim : (filteredHilbertPolynomial IL).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdim
  have hILdegree : (filteredHilbertPolynomial IL).leadingCoeff = (d : ℚ) / m.factorial := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hdegree
  obtain ⟨hdense,hopen⟩ := fixedCoordinateBirationalSubspaceLocus_plucker_dense_open
    IL hmn d hILdim hILdegree e
  refine ⟨s,e,Φ,hhom,hdeg,hstrict,hboundary,?_,hdense,hopen⟩
  have he' : birationalCenterSubspaceLocus (projectiveClosureIdeal IL) e =
      (centerPluckerFamilyZeroLocus (algebraMap K L) Φ)ᶜ :=
    (birationalCenterSubspaceLocus_congr _ _
      (projectiveClosureIdeal_scalar_extension (L := L) I) e).symm.trans he
  change Subtype.val ⁻¹' birationalCenterSubspaceLocus
    (projectiveClosureIdeal IL) e = _
  rw [he']
  rfl

end
end CCDN
