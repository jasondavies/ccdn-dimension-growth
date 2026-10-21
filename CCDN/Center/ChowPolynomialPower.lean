/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CCDN.Determinant.HypersurfaceSmoothPoint
import CCDN.Determinant.SingularDeterminant
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Nullstellensatz
import CCDN.ForMathlib.MvPolynomial
/-! The algebraic power step in the Chow-form projection argument. Equal
geometric zero loci with an irreducible equation force a positive power,
including the nonzero scalar omitted when Chow forms are normalized. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A polynomial with the same geometric hypersurface as an irreducible
polynomial is a nonzero constant times a positive power. -/
theorem polynomial_eq_scalar_pow_of_same_zeros
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (F R : MvPolynomial σ K) (hF : Irreducible F)
    (hzero : ∀ z : σ → K, eval z R = 0 ↔ eval z F = 0) :
    ∃ (a : K) (r : ℕ), a ≠ 0 ∧ 0 < r ∧ R = C a * F ^ r := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span {R}
  have hm : F ∈ vanishingIdeal K (MvPolynomial.zeroLocus K J) := by
    intro z hz
    rw [aeval_eq_eval]
    apply (hzero z).mp
    have hh := hz R (Ideal.subset_span (Set.mem_singleton R))
    simpa only [aeval_eq_eval] using hh
  rw [vanishingIdeal_zeroLocus_eq_radical] at hm
  obtain ⟨N,hN⟩ := hm
  have hdiv : R ∣ F ^ N := Ideal.mem_span_singleton.mp hN
  obtain ⟨r,_,hr⟩ := (dvd_prime_pow hF.prime N).mp hdiv
  have hFR : F ∣ R := by
    by_contra hh
    obtain ⟨z,hz,hzR⟩ := exists_hypersurface_point_eval_ne_zero F R hF hh
    exact hzR ((hzero z).mpr hz)
  have hrpos : 0 < r := by
    by_contra hh
    have hr0 : r = 0 := by omega
    have hunit : IsUnit R := by
      rw [hr0,pow_zero] at hr
      exact associated_one_iff_isUnit.mp hr
    exact hF.not_isUnit (isUnit_of_dvd_unit hFR hunit)
  obtain ⟨u,hu⟩ := hr.symm
  obtain ⟨a,ha,huC⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  refine ⟨a,r,isUnit_iff_ne_zero.mp ha,hrpos,?_⟩
  rw [← hu,huC,mul_comm]

/-- The source's pushforward irreducibility test reduces to equality of
total degrees, once the geometric incidence zero loci agree. -/
theorem irreducible_iff_degree_eq_of_same_zeros
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (F R : MvPolynomial σ K) (hF : Irreducible F)
    (hzero : ∀ z : σ → K, eval z R = 0 ↔ eval z F = 0) :
    Irreducible R ↔ R.totalDegree = F.totalDegree := by
  obtain ⟨a,r,ha,hr,he⟩ := polynomial_eq_scalar_pow_of_same_zeros F R hF hzero
  have hunit : IsUnit (C a : MvPolynomial σ K) := (isUnit_iff_ne_zero.mpr ha).map C
  have hdpos := MvPolynomial.totalDegree_pos_of_irreducible hF
  have hpow (j : ℕ) : (F ^ j).totalDegree = j * F.totalDegree := by
    induction j with
    | zero => simp
    | succ k hk =>
      rw [pow_succ,totalDegree_mul_of_isDomain (pow_ne_zero _ hF.ne_zero) hF.ne_zero,hk]
      ring
  have hdegree : R.totalDegree = r * F.totalDegree := by
    rw [he,totalDegree_mul_of_isDomain (C_eq_zero.not.mpr ha) (pow_ne_zero _ hF.ne_zero),
      totalDegree_C,zero_add,hpow r]
  constructor
  · intro hR
    have hp : Irreducible (F ^ r) := (irreducible_isUnit_mul hunit).mp (he ▸ hR)
    have hone : r = 1 := by by_contra hh; exact not_irreducible_pow hh hp
    simpa only [hone,one_mul] using hdegree
  · intro hd
    have hone : r = 1 := by nlinarith
    rw [he,hone,pow_one]
    exact (irreducible_isUnit_mul hunit).mpr hF

end
end CCDN
