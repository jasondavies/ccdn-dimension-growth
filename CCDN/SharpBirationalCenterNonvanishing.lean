module

public import CCDN.SharpCenterExtensionDetector
public import CCDN.BirationalMinorCenterWitness
public import CCDN.ProjectiveClosureHilbertPolynomial
public import CCDN.PolynomialPredicates

/-! A member of the sharp resultant detector family that is nonzero at a
given good center. Every independent center at which it is nonzero is good. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

theorem exists_nonzero_sharp_center_detector
    {K : Type*} [Field K] [CharZero K] {n m r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) [J.IsPrime]
    [(J.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hJ : IsHomogeneousIdeal J)
    (d : ℕ) (hdim : (filteredHilbertPolynomial J).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial J).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (hr : r + 2 ≤ n + 2)
    (A : Matrix (Fin r) (Fin (n + 2)) K) (hA : LinearIndependent K A.row)
    (hgood : IsBirationalMatrixCenter J A) :
    ∃ G : MvPolynomial (Fin r ↪ Fin (n + 2)) K,
      G.IsHomogeneous (((m + 1) * d) * (2 * d - 1)) ∧
      G.totalDegree ≤ ((m + 1) * d) * (2 * d - 1) ∧
      eval (matrixPluckerCoordinates A) G ≠ 0 ∧
      ∀ B : Matrix (Fin r) (Fin (n + 2)) K, LinearIndependent K B.row →
        eval (matrixPluckerCoordinates B) G ≠ 0 → IsBirationalMatrixCenter J B := by
  obtain ⟨Φ, hhom, hdeg, hΦ⟩ := exists_sharp_birational_center_detector J hJ d hdim hdegree hr
  obtain ⟨G, hG, heval⟩ := (hΦ A hA).mpr hgood
  exact ⟨G, hhom G hG, hdeg G hG, heval, fun B hB hGB => (hΦ B hB).mp ⟨G, hG, hGB⟩⟩

end
end CCDN
