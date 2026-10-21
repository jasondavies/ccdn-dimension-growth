module

public import CCDN.Hilbert.HomogeneousFilteredRank
public import CCDN.Algebra.PolynomialPredicates
/-! A quadratic Hilbert polynomial of a homogeneous affine cone gives the
linear projective Hilbert function, with exactly the same degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma quadratic_polynomial_successive_difference
    (P : Polynomial ℚ) (d : ℕ) (hd : P.natDegree = 2)
    (hlc : P.leadingCoeff = (d : ℚ) / 2) (x y : ℚ) :
    (P.eval (x + 1) - P.eval x) - (P.eval (y + 1) - P.eval y) =
      (d : ℚ) * (x - y) := by
  have hc : P.coeff 2 = (d : ℚ) / 2 := by
    rw [← hd, ← Polynomial.leadingCoeff, hlc]
  have heval (z : ℚ) :
      P.eval z = P.coeff 0 + P.coeff 1 * z + (d : ℚ) / 2 * z ^ 2 := by
    rw [Polynomial.eval_eq_sum_range' (show P.natDegree < 3 by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one, hc]
  rw [heval, heval, heval, heval]
  ring

theorem projectiveCurveDegree_of_filteredHilbertPolynomial
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 2)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / 2) :
    HasProjectiveCurveDegree I d := by
  obtain ⟨T, hT⟩ := filteredHilbertPolynomial_spec I
  have hgrad (N : ℕ) (hN : T ≤ N) :
      (projectiveHilbertFunction I (N + 1) : ℚ) =
        (filteredHilbertPolynomial I).eval ((N : ℚ) + 1) -
          (filteredHilbertPolynomial I).eval (N : ℚ) := by
    rw [show (N : ℚ) + 1 = ((N + 1 : ℕ) : ℚ) by push_cast; rfl,
      hT (N + 1) (by omega), hT N hN]
    have hh : (Module.finrank K (filteredCoordinateSpace I (N + 1)) : ℚ) =
        Module.finrank K (filteredCoordinateSpace I N) +
          projectiveHilbertFunction I (N + 1) := by
      exact_mod_cast filteredCoordinateSpace_finrank_succ I hI N
    linarith
  refine ⟨T + 1, (projectiveHilbertFunction I (T + 1) : ℤ) - d * (T + 1), ?_⟩
  intro M hM
  cases M with
  | zero => omega
  | succ N =>
    have hh := quadratic_polynomial_successive_difference
      (filteredHilbertPolynomial I) d hdim hdegree (N : ℚ) (T : ℚ)
    rw [← hgrad N (by omega), ← hgrad T le_rfl] at hh
    have he : (projectiveHilbertFunction I (N + 1) : ℚ) =
        (d : ℚ) * (N + 1) +
          ((projectiveHilbertFunction I (T + 1) : ℚ) - d * (T + 1)) := by
      linarith
    exact_mod_cast he

end
end CCDN
