module

public import CCDN.RationalDifferential

/-! Bounded-degree differential constants in positive characteristic.
Unlike characteristic zero, the degree restrictions are essential. These
lemmas isolate the constant-descent step in Gao's differential criterion;
they do not supply the resultant bounds for residues or a Bertini theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

lemma polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (f : K[X]) (hdeg : f.natDegree < p) (hder : f.derivative = 0) :
    f = C (f.coeff 0) := by
  ext i
  by_cases hi : i = 0
  · subst i; simp
  · rw [coeff_C, ite_eq_right hi]
    by_cases hlarge : f.natDegree < i
    · exact coeff_eq_zero_of_natDegree_lt hlarge
    · have hip : i < p := lt_of_le_of_lt (Nat.le_of_not_gt hlarge) hdeg
      have hiK : (i : K) ≠ 0 := by
        intro h
        have hdiv := (CharP.cast_eq_zero_iff K p i).mp h
        exact hi (Nat.eq_zero_of_dvd_of_lt hdiv hip)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have h := congrArg (fun q : K[X] => q.coeff j) hder
      simp only [coeff_derivative, coeff_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by simpa only [Nat.cast_succ] using hiK)

/-- For a reduced rational fraction, zero derivative forces both numerator
and denominator derivatives to vanish, in every characteristic. -/
theorem rationalDerivative_num_denom_eq_zero
    {K : Type*} [Field K] (x : RatFunc K) (hx : rationalDerivative x = 0) :
    x.num.derivative = 0 ∧ x.denom.derivative = 0 := by
  have hfrac : rationalDerivativeFraction x.num x.denom = 0 := by
    rw [← rationalDerivative_div, x.num_div_denom]
    exact hx
  have hden := RatFunc.algebraMap_ne_zero x.denom_ne_zero
  have hnum : algebraMap K[X] (RatFunc K) x.num.derivative * algebraMap K[X] (RatFunc K) x.denom -
      algebraMap K[X] (RatFunc K) x.num * algebraMap K[X] (RatFunc K) x.denom.derivative = 0 :=
    (div_eq_zero_iff.mp hfrac).resolve_right (pow_ne_zero 2 hden)
  have he : x.num.derivative * x.denom = x.num * x.denom.derivative := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using sub_eq_zero.mp hnum
  have hdvd : x.denom ∣ x.denom.derivative := by
    apply x.isCoprime_num_denom.symm.dvd_of_dvd_mul_left
    rw [← he]
    exact dvd_mul_left _ _
  have hdz : x.denom.derivative = 0 := by
    by_contra hn
    exact (not_le_of_gt (degree_derivative_lt x.denom_ne_zero)) (degree_le_of_dvd hdvd hn)
  refine ⟨?_, hdz⟩
  rw [hdz, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_right x.denom_ne_zero

/-- A rational function whose reduced numerator and denominator have degree
below the characteristic is constant if its derivative vanishes. -/
theorem rationalDerivative_mem_base_of_degree_lt_char
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (x : RatFunc K) (hnum : x.num.natDegree < p) (hden : x.denom.natDegree < p)
    (hx : rationalDerivative x = 0) :
    x ∈ (algebraMap K (RatFunc K)).range := by
  obtain ⟨hnz, hdz⟩ := rationalDerivative_num_denom_eq_zero x hx
  refine ⟨x.num.coeff 0 / x.denom.coeff 0, ?_⟩
  conv_rhs =>
    rw [← x.num_div_denom,
      polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char x.num hnum hnz,
      polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char x.denom hden hdz]
  simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, map_div₀]

/-- Positive-characteristic constant descent with explicit bounds on the
reduced rational coefficients of the minimal polynomial. Establishing
these bounds for a closed-form residue is a separate resultant calculation. -/
theorem algebraic_differential_constant_mem_base_of_coeff_degree_lt_char
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] {p : ℕ} [CharP F p]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] {x : L} (hx : IsIntegral (RatFunc F) x)
    (hdegree : ∀ i, ((minpoly (RatFunc F) x).coeff i).num.natDegree < p ∧
      ((minpoly (RatFunc F) x).coeff i).denom.natDegree < p) :
    let := rationalDifferential F
    DifferentialAlgebra (RatFunc F) L → x′ = 0 → x ∈ (algebraMap F L).range := by
  dsimp only
  let := rationalDifferential F
  intro hdiff hder
  have := hdiff
  have hcoeff : ∀ i, (minpoly (RatFunc F) x).coeff i ∈ Set.range (algebraMap F (RatFunc F)) := by
    intro i
    apply rationalDerivative_mem_base_of_degree_lt_char _ (hdegree i).1 (hdegree i).2
    have h := congrArg (fun q : (RatFunc F)[X] => q.coeff i) (minpoly_mapCoeffs_eq_zero hx hder)
    simp only [Differential.coeff_mapCoeffs, coeff_zero] at h
    change rationalDerivative _ = 0 at h
    exact h
  obtain ⟨q, hq⟩ := (mem_lifts (f := algebraMap F (RatFunc F)) (minpoly (RatFunc F) x)).mp
    ((lifts_iff_coeff_lifts _).mpr hcoeff)
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hq
    exact (minpoly.ne_zero hx) hq.symm
  have hroot : (q.map (algebraMap F L)).IsRoot x := by
    change eval x (q.map (algebraMap F L)) = 0
    rw [eval_map]
    change aeval x q = 0
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq F (RatFunc F) L).symm, hq]
    exact minpoly.aeval (RatFunc F) x
  exact (IsAlgClosed.splits q).mem_range_of_isRoot hq0 hroot

end
end CCDN
