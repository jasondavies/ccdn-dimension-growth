module

public import AffineCurveCounting.BoundedDifferentialConstants
public import AffineCurveCounting.DifferentialResidue

/-! A low-degree algebraic relation detects differential constants.
If t'=1 in characteristic p, no nonzero polynomial in t of degree below p
can have differential-constant coefficients and vanish. Applied to a
bivariate relation, this gives constant descent directly from elimination. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Differential
open scoped Differential

theorem polynomial_eq_zero_of_differential_constant_coefficients
    {L : Type*} [Field L] [Differential L] {p : ℕ} [CharP L p]
    (t : L) (ht : t′ = 1) (f : L[X]) (hdeg : f.natDegree < p)
    (hcoeff : Differential.mapCoeffs f = 0) (hroot : f.eval t = 0) :
    f = 0 := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hn0 : n = 0
    · have he := eq_C_of_natDegree_eq_zero (hn.trans hn0)
      rw [he, eval_C] at hroot
      rw [he, hroot, C_0]
    · have hderroot : f.derivative.eval t = 0 := by
        have h := Differential.deriv_aeval_eq t f
        simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at h
        rw [hroot, map_zero, hcoeff, eval_zero, ht, mul_one, zero_add] at h
        exact h.symm
      have hdercoeff : Differential.mapCoeffs f.derivative = 0 := by
        rw [← derivative_differential_mapCoeffs, hcoeff, derivative_zero]
      have hlt : f.derivative.natDegree < n := by
        rw [← hn]
        exact natDegree_derivative_lt (by omega)
      have hdz := ih f.derivative.natDegree hlt f.derivative
        (by omega) hdercoeff hderroot rfl
      have he := polynomial_eq_C_of_derivative_eq_zero_of_degree_lt_char f hdeg hdz
      rw [he, eval_C] at hroot
      rw [he, hroot, C_0]

lemma differential_aeval_eq_zero_of_constants
    {F L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (x : L) (hx : x′ = 0) (f : F[X]) :
    (aeval x f)′ = 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | monomial n a =>
    rw [aeval_monomial]
    simp [Derivation.leibniz, hbase, hx]

/-- A differential constant satisfying a nonzero bivariate relation of
t-degree below the characteristic lies in the algebraically closed base.
The inner variable represents the constant; the outer variable represents t. -/
theorem differential_constant_mem_base_of_relation
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    [Differential L] {p : ℕ} [CharP L p]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (t x : L) (ht : t′ = 1) (hx : x′ = 0)
    (R : F[X][X]) (hR : R ≠ 0) (hdeg : R.natDegree < p)
    (hroot : (R.map (aeval x).toRingHom).eval t = 0) :
    x ∈ (algebraMap F L).range := by
  have hmap : Differential.mapCoeffs (R.map (aeval x).toRingHom) = 0 := by
    ext i
    simp only [Differential.coeff_mapCoeffs, coeff_map, coeff_zero]
    exact differential_aeval_eq_zero_of_constants hbase x hx _
  have hz := polynomial_eq_zero_of_differential_constant_coefficients t ht
    (R.map (aeval x).toRingHom) (natDegree_map_le.trans_lt hdeg) hmap hroot
  let i := R.natDegree
  have hi : R.coeff i ≠ 0 := by simpa only [i, coeff_natDegree] using leadingCoeff_ne_zero.mpr hR
  have hiRoot : ((R.coeff i).map (algebraMap F L)).IsRoot x := by
    have h := congrArg (fun f : L[X] => f.coeff i) hz
    simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      IsRoot, eval_map, aeval_def] using h
  exact (IsAlgClosed.splits (R.coeff i)).mem_range_of_isRoot hi hiRoot

end
end AffineCurveCounting
