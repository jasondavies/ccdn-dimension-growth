module

public import AffineCurveCounting.BirationalCenterDensity

/-! Actual disjoint birational centers form a dense open locus even after
requiring the center to lie in X0=0. The witness is constructed from the
affine variety; ambient density alone is not used for this restriction. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

abbrev FixedCoordinateCenterMatrix (K : Type*) [Field K] (r n : ℕ) :=
  {x : Fin r × Fin (n + 1) → K //
    (∀ i j, j ∈ ({0} : Finset (Fin (n + 1))) → x (i,j) = 0) ∧
    LinearIndependent K (fun i : Fin r => fun j : Fin (n + 1) => x (i,j))}

def fixedCoordinateBirationalCenterLocus
    {K : Type*} [Field K] {n r s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    Set (FixedCoordinateCenterMatrix K r n) :=
  {x | IsBirationalMatrixCenter (projectiveClosureIdeal I) e
    (Matrix.of fun i j => x.val (i,j))}

theorem fixedCoordinateBirationalCenterLocus_isOpen
    {K : Type*} [Field K] [CharZero K] {n m r s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (hr : r + 2 ≤ n + 2)
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 2))) :
    IsOpen (fixedCoordinateBirationalCenterLocus I e) := by
  have := projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure K) I
  obtain ⟨hcdim,hcdeg⟩ := projectiveClosureIdeal_hilbertPolynomial_parameters I m d hdim hdegree
  have hop := birationalMatrixCenterLocus_isOpen (projectiveClosureIdeal I)
    (projectiveClosureIdeal_homogeneous I) d hcdim hcdeg hr e
  let forget : FixedCoordinateCenterMatrix K r (n + 1) →
      IndependentCenterMatrix K r (n + 2) := fun x => ⟨x.val,x.property.2⟩
  have hf : Continuous forget := continuous_subtype_val.subtype_mk _
  exact hop.preimage hf

theorem fixedCoordinateBirationalCenterLocus_dense
    {K : Type*} [Field K] [CharZero K] {n m s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (fixedCoordinateBirationalCenterLocus I e) := by
  obtain ⟨t,e',G,A,_,_,hA,hA0,hG,hgood⟩ :=
    exists_nonzero_fixed_coordinate_center_detector I hmn d hdim hdegree
  have hAz : ∀ i j, j ∈ ({0} : Finset (Fin (n + 2))) → A i j = 0 := by
    intro i j hj
    simpa only [Finset.mem_singleton.mp hj] using hA0 i
  have hp : zeroColumnSubstitution {0} (centerMinorPolynomial G) ≠ 0 := by
    intro hz
    have he := congrArg (eval (fun q => A q.1 q.2)) hz
    rw [eval_zeroColumnSubstitution,zeroColumnPoint_fixed {0} _ hAz,
      eval_centerMinorPolynomial,map_zero] at he
    exact hG he
  apply (zero_column_polynomial_locus_dense_subspace {0} A hA hAz _ hp).mono
  intro x hx
  change IsBirationalMatrixCenter (projectiveClosureIdeal I) e
    (Matrix.of fun i j => x.val (i,j))
  apply (isBirationalMatrixCenter_iff_enumeration (projectiveClosureIdeal I)
    e e' _ x.property.2).mpr
  apply hgood _ x.property.2
  change eval x.val (centerMinorPolynomial G) ≠ 0 at hx
  rwa [eval_centerMinorPolynomial] at hx

theorem fixedCoordinateBirationalCenterLocus_dense_open
    {K : Type*} [Field K] [CharZero K] {n m s : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (e : Fin (s + 2) ≃ (Fin (n + 1 - m - 1 + 1) ↪ Fin (n + 2))) :
    Dense (fixedCoordinateBirationalCenterLocus I e) ∧
      IsOpen (fixedCoordinateBirationalCenterLocus I e) :=
  ⟨fixedCoordinateBirationalCenterLocus_dense I hmn d hdim hdegree e,
    fixedCoordinateBirationalCenterLocus_isOpen I d hdim hdegree (by omega) e⟩

end
end AffineCurveCounting
