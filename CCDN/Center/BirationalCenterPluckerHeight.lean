module

public import CCDN.Center.IntegerMinorProjectiveHeight
public import CCDN.Center.BoundedGoodCenter
public import CCDN.Center.ZeroColumnCenterSubspace
public import CCDN.Algebra.PolynomialPredicates
/-! Bounded rational good centers in the intrinsic Plücker height. The
center, its good-locus membership and its height bound are constructed
simultaneously from the source variety, including centers in X0=0. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem integer_center_subspace_plucker_height {r n T : ℕ}
    (M : Matrix (Fin r) (Fin n) ℤ)
    (hM : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row)
    (hb : ∀ i j, |M i j| ≤ (T : ℤ)) :
    (centerSubspacePlucker (centerMatrixSpan
      (⟨fun q => (M q.1 q.2 : ℚ), hM⟩ : IndependentCenterMatrix ℚ r n))).mulHeight ≤
      (r.factorial * T ^ r : ℕ) := by
  rw [centerSubspacePlucker_matrixSpan, independentCenterPlucker,
    Projectivization.mulHeight_mk]
  have hh := integer_maximal_minor_projective_height M hM hb
  rw [Projectivization.mulHeight_mk] at hh
  have he : matrixPluckerCoordinates
      (Matrix.of fun i j => (M i j : ℚ)) =
      (fun c : Fin r ↪ Fin n => ((M.submatrix id c).det : ℚ)) := by
    funext c
    exact (RingHom.map_det (Int.castRingHom ℚ) (M.submatrix id c)).symm
  rwa [he]

/-- Lemma 5.3 for the good-center subspace and its intrinsic Plücker
height. The degree-one and zero-dimensional cases are included. -/
theorem exists_birational_center_plucker_height
    {n m : ℕ} (hmn : m + 2 ≤ n + 1)
    (J : Ideal (MvPolynomial (Fin (n + 2)) ℚ)) [J.IsPrime]
    [(J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree J m d) :
    ∃ W ∈ birationalCenterSubspaceLocus (r := n + 1 - m - 1) J,
      (centerSubspacePlucker W).mulHeight ≤
        (centerMinorBound (n + 1 - m - 1) m d : ℕ) := by
  obtain ⟨M,hM,_,hli,hgood⟩ :=
    exists_bounded_integer_birational_center hmn J hJ d hdimdeg
  let x : IndependentCenterMatrix ℚ (n + 1 - m - 1) (n + 2) :=
    ⟨fun q => (M q.1 q.2 : ℚ), hli⟩
  refine ⟨centerMatrixSpan x, ⟨x,hgood,rfl⟩, ?_⟩
  exact integer_center_subspace_plucker_height M hli
    (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2)

/-- The intrinsic-height good center can be constructed inside X0=0.
This includes the empty center when the affine source is a hypersurface. -/
theorem exists_fixed_coordinate_center_plucker_height
    {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime]
    (hmn : m + 1 ≤ n + 1) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    ∃ W ∈ fixedCoordinateBirationalSubspaceLocus (r := n + 1 - m - 1) I,
      (centerSubspacePlucker W.val).mulHeight ≤
        (centerMinorBound (n + 1 - m - 1) m d : ℕ) := by
  obtain ⟨M,hM,_,hM0,hli,hgood⟩ :=
    exists_bounded_integer_fixed_coordinate_center I hmn d hdim hdegree
  let x : FixedCoordinateCenterMatrix ℚ (n + 1 - m - 1) (n + 1) :=
    ⟨fun q => (M q.1 q.2 : ℚ),
      (by intro i j hj; simp only [Finset.mem_singleton.mp hj, hM0, Int.cast_zero]), hli⟩
  refine ⟨zeroColumnMatrixSpan x, ?_, ?_⟩
  · change x ∈ zeroColumnMatrixSpan ⁻¹' fixedCoordinateBirationalSubspaceLocus I
    rw [fixedCoordinateBirationalSubspaceLocus_preimage]
    exact hgood
  · exact integer_center_subspace_plucker_height M hli
      (fun i j => by rw [abs_of_nonneg (hM i j).1]; exact (hM i j).2)

end
end CCDN
