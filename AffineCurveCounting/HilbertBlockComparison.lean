module

public import AffineCurveCounting.HilbertPolynomialComparison

/-! Independent polynomial blocks compare with the actual Hilbert
multiplicity. A fixed filtration shift does not change the leading term. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

theorem hilbert_block_count_le_multiplicity
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) (m d r D : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial)
    (hlow : ∀ N, r * (m + N).choose m ≤
      Module.finrank K (filteredCoordinateSpace I (D + N))) : r ≤ d := by
  by_cases hr : r = 0
  · omega
  let P := Polynomial.C (r : ℚ) * Polynomial.preHilbertPoly ℚ m 0
  let Q := (filteredHilbertPolynomial I).comp (Polynomial.X + Polynomial.C (D : ℚ))
  have hPdeg : P.natDegree = m := by
    dsimp only [P]
    rw [Polynomial.natDegree_C_mul (by exact_mod_cast hr),
      Polynomial.natDegree_preHilbertPoly]
  have hQdeg : Q.natDegree = m := by
    simp only [Q, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hdim]
  have hPlc : P.leadingCoeff = (r : ℚ) / m.factorial := by
    dsimp only [P]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_preHilbertPoly, div_eq_mul_inv]
  have hQlc : Q.leadingCoeff = (filteredHilbertPolynomial I).leadingCoeff := by
    dsimp only [Q]
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hPpos : 0 < P.leadingCoeff := by rw [hPlc]; positivity
  have hQpos : 0 < Q.leadingCoeff := by
    rw [hQlc]
    exact filteredHilbertPolynomial_leadingCoeff_pos I hI
  have hh := polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hPpos hQpos
    (hPdeg.trans hQdeg.symm) (by
      obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
      refine ⟨M, fun N hN => ?_⟩
      simp only [P, Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X]
      rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ m (by omega : 0 ≤ N + m),
        show (N : ℚ) + D = ((D + N : ℕ) : ℚ) by push_cast; ring,
        hM (D + N) (by omega)]
      simp only [Nat.sub_zero, Nat.add_comm N m]
      exact_mod_cast hlow N)
  rw [hPlc, hQlc, hdegree] at hh
  exact_mod_cast (div_le_div_iff_of_pos_right
    (by positivity : (0 : ℚ) < m.factorial)).mp hh

end
end AffineCurveCounting
