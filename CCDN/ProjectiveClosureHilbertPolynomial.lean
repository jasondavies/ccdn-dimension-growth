module

public import CCDN.ProjectiveClosureDegree
public import CCDN.HomogeneousFilteredRank
public import CCDN.ForMathlib.Polynomial

/-! The projective closure raises filtered Hilbert dimension by one
and preserves factorial-normalized multiplicity in every dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem projectiveClosureIdeal_hilbertPolynomial_difference
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    (filteredHilbertPolynomial (projectiveClosureIdeal I)).comp
        (Polynomial.X + Polynomial.C 1) -
      filteredHilbertPolynomial (projectiveClosureIdeal I) =
        (filteredHilbertPolynomial I).comp (Polynomial.X + Polynomial.C 1) := by
  apply polynomial_eq_of_eventual_nat_eval_eq
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec (projectiveClosureIdeal I)
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  refine ⟨max N M, fun k hk => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [show (k : ℚ) + 1 = ((k + 1 : ℕ) : ℚ) by push_cast; rfl,
    hN (k + 1) (by omega), hN k (by omega), hM (k + 1) (by omega)]
  have hh := filteredCoordinateSpace_finrank_succ (projectiveClosureIdeal I)
    (projectiveClosureIdeal_homogeneous I) k
  rw [projectiveClosureIdeal_hilbertFunction] at hh
  have hhQ :
    (Module.finrank K (filteredCoordinateSpace (projectiveClosureIdeal I) (k + 1)) : ℚ) =
      Module.finrank K (filteredCoordinateSpace (projectiveClosureIdeal I) k) +
        Module.finrank K (filteredCoordinateSpace I (k + 1)) := by exact_mod_cast hh
  linarith

/-- Both dimension and multiplicity are computed from the closure ideal and
its Hilbert functions. -/
theorem projectiveClosureIdeal_hilbertPolynomial_parameters
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (m d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / m.factorial) :
    (filteredHilbertPolynomial (projectiveClosureIdeal I)).natDegree = m + 1 ∧
      (filteredHilbertPolynomial (projectiveClosureIdeal I)).leadingCoeff =
        (d : ℚ) / (m + 1).factorial := by
  let P := filteredHilbertPolynomial (projectiveClosureIdeal I)
  let Q := filteredHilbertPolynomial I
  have he : P.comp (Polynomial.X + Polynomial.C 1) - P =
      Q.comp (Polynomial.X + Polynomial.C 1) :=
    projectiveClosureIdeal_hilbertPolynomial_difference I
  have hQlc : (Q.comp (Polynomial.X + Polynomial.C 1)).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_X_add_C,
      one_pow, mul_one]
  have hQne : Q.comp (Polynomial.X + Polynomial.C 1) ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [hQlc]
    exact ne_of_gt (filteredHilbertPolynomial_leadingCoeff_pos I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
  have hPpos : 0 < P.natDegree := by
    by_contra h
    have hP : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    rw [hP, Polynomial.C_comp, sub_self] at he
    exact hQne he.symm
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPpos)
  have hf := And.intro (Polynomial.natDegree_comp_X_add_C_sub_self P hr 1 one_ne_zero)
    (Polynomial.leadingCoeff_comp_X_add_C_sub_self P hr 1 one_ne_zero)
  rw [he] at hf
  have hrm : r = m := by
    have hdeg : (Q.comp (Polynomial.X + Polynomial.C 1)).natDegree = m := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      exact hdim
    omega
  subst r
  refine ⟨hr, ?_⟩
  have hc : Q.leadingCoeff = P.leadingCoeff * (m + 1) := by
    simpa only [hQlc, mul_one] using hf.2
  change P.leadingCoeff = _
  change Q.leadingCoeff = _ at hdegree
  rw [hdegree] at hc
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hm : (m + 1 : ℚ) ≠ 0 := by positivity
  have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp at hc ⊢
  push_cast
  nlinarith

end
end CCDN
