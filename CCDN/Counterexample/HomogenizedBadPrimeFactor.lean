/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.LiteralAffineBadPrimes
import Mathlib.Algebra.MvPolynomial.Division

/-! Homogenization changes the bad-prime factor of CCDN Definition 3.2.1.
The proof of Proposition 4.2.1 replaces an affine equation `f` by its homogenization `F₁`
and uses `b(F₁) = b(f)`. For `f = c x₁² + x₂` every reduction is absolutely irreducible, so
`b(f) = 1`, while `F₁ = c x₁² + x₀ x₂` reduces to `x₀ x₂` modulo every prime factor of `c`.
For `c = 439 > 27 · 2⁴` this gives `b(F₁) = 439^(1/439)`, and products of primes above `432`
make `b(F₁)` unbounded. Here `b` is `literalAffineBadPrimeFactor`, Definition 3.2.1 read
literally: a prime is bad only when the reduction is not absolutely irreducible, so the degree
drop of `f` modulo the prime factors of `c` is not counted for `f`, while for the homogeneous
`F₁` the same primes give reducible reductions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine equation `c x₁² + x₂`. -/
def badPrimeAffineExample (c : ℤ) : MvPolynomial (Fin 2) ℤ := C c * X 0 ^ 2 + X 1

/-- The homogenization `c x₁² + x₀ x₂` of `badPrimeAffineExample c`, with `x₀` the
coordinate at infinity as in `scaledHomogenize`. -/
def badPrimeHomogenizedExample (c : ℤ) : MvPolynomial (Fin 3) ℤ := C c * X 1 ^ 2 + X 0 * X 2

lemma irreducible_of_irreducible_algEquiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {x : A}
    (h : Irreducible (e x)) : Irreducible x :=
  (MulEquiv.irreducible_iff (e : A ≃* B)).mp h

/-- An equation linear in one variable with constant coefficient is irreducible. -/
lemma irreducible_C_mul_X_sq_add_X {K : Type*} [Field K] (a : K) :
    Irreducible (C a * X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) K) := by
  let e := (renameEquiv K (Equiv.swap (0 : Fin 2) 1)).trans (finSuccEquiv K 1)
  have he : e (C a * X 0 ^ 2 + X 1) = Polynomial.X + Polynomial.C (C a * X 0 ^ 2) := by
    have h1 : finSuccEquiv K 1 (X 1) = Polynomial.C (X 0) := by
      simpa using finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
    have hC : finSuccEquiv K 1 (C a) = Polynomial.C (C a) := (finSuccEquiv K 1).commutes a
    simp [e, h1, hC, finSuccEquiv_X_zero]
    ring
  apply irreducible_of_irreducible_algEquiv e
  rw [he]
  exact (Polynomial.monic_X_add_C _).irreducible_of_degree_eq_one (Polynomial.degree_X_add_C _)

/-- The nondegenerate quadric `a x₁² + x₀ x₂` is irreducible. -/
lemma irreducible_C_mul_X_sq_add_X_mul_X {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Irreducible (C a * X 1 ^ 2 + X 0 * X 2 : MvPolynomial (Fin 3) K) := by
  let e := finSuccEquiv K 2
  have he : e (C a * X 1 ^ 2 + X 0 * X 2) =
      Polynomial.C (X 1) * Polynomial.X + Polynomial.C (C a * X 0 ^ 2) := by
    have h1 : finSuccEquiv K 2 (X 1) = Polynomial.C (X 0) := by
      simpa using finSuccEquiv_X_succ (R := K) (n := 2) (j := 0)
    have h2 : finSuccEquiv K 2 (X 2) = Polynomial.C (X 1) := by
      simpa using finSuccEquiv_X_succ (R := K) (n := 2) (j := 1)
    have hC : finSuccEquiv K 2 (C a) = Polynomial.C (C a) := (finSuccEquiv K 2).commutes a
    simp [e, h1, h2, hC, finSuccEquiv_X_zero]
    ring
  apply irreducible_of_irreducible_algEquiv e
  rw [he]
  apply Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff
    (Polynomial.degree_linear (X_ne_zero _))
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ite_true,
    one_ne_zero, ite_false, add_zero]
  refine ((X_prime.irreducible).isRelPrime_iff_not_dvd.mpr fun h => ha ?_).symm
  simpa using map_dvd (eval ![1, 0]) h

lemma map_badPrimeAffineExample {K : Type*} [CommRing K] (c : ℤ) :
    map (Int.castRingHom K) (badPrimeAffineExample c) = C (c : K) * X 0 ^ 2 + X 1 := by
  simp [badPrimeAffineExample]

lemma map_badPrimeHomogenizedExample {K : Type*} [CommRing K] (c : ℤ) :
    map (Int.castRingHom K) (badPrimeHomogenizedExample c) = C (c : K) * X 1 ^ 2 + X 0 * X 2 := by
  simp [badPrimeHomogenizedExample]

lemma totalDegree_badPrimeAffineExample {c : ℤ} (hc : c ≠ 0) :
    (badPrimeAffineExample c).totalDegree = 2 := by
  have h2 : (C c * X 0 ^ 2 : MvPolynomial (Fin 2) ℤ).totalDegree = 2 := by
    rw [C_mul_X_pow_eq_monomial, totalDegree_monomial _ hc]
    simp
  unfold badPrimeAffineExample
  rw [totalDegree_add_eq_left_of_totalDegree_lt (by rw [h2, totalDegree_X]; norm_num), h2]

lemma isHomogeneous_badPrimeHomogenizedExample (c : ℤ) :
    (badPrimeHomogenizedExample c).IsHomogeneous 2 :=
  ((isHomogeneous_C _ c).mul (isHomogeneous_X_pow 1 2)).add
    ((isHomogeneous_X _ 0).mul (isHomogeneous_X _ 2))

/-- `badPrimeHomogenizedExample c` is the homogenization of `badPrimeAffineExample c`. -/
theorem scaledHomogenize_badPrimeAffineExample {c : ℤ} (hc : c ≠ 0) :
    scaledHomogenize 2 1 (badPrimeAffineExample c) = badPrimeHomogenizedExample c := by
  apply affineChart_injective_on_homogeneous
    (scaledHomogenize_homogeneous 1 _ (totalDegree_badPrimeAffineExample hc).le)
    (isHomogeneous_badPrimeHomogenizedExample c)
  rw [affineChart_scaledHomogenize_one]
  have h1 : affineChart 2 (X 1 : MvPolynomial (Fin 3) ℤ) = X 0 := eval₂_X _ _ _
  have h2 : affineChart 2 (X 2 : MvPolynomial (Fin 3) ℤ) = X 1 := eval₂_X _ _ _
  have h0 : affineChart 2 (X 0 : MvPolynomial (Fin 3) ℤ) = 1 := eval₂_X _ _ _
  simp [badPrimeAffineExample, badPrimeHomogenizedExample, h0, h1, h2]

lemma totalDegree_badPrimeHomogenizedExample {c : ℤ} (hc : c ≠ 0) :
    (badPrimeHomogenizedExample c).totalDegree = 2 := by
  rw [← scaledHomogenize_badPrimeAffineExample hc]
  apply (scaledHomogenize_homogeneous 1 _ (totalDegree_badPrimeAffineExample hc).le).totalDegree
  intro h
  have := congrArg (affineChart 2) h
  rw [affineChart_scaledHomogenize_one, map_zero] at this
  have hd := totalDegree_badPrimeAffineExample hc
  rw [this, totalDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- Every reduction of `c x₁² + x₂` is absolutely irreducible, so `b(f) = 1`. -/
theorem literalAffineBadPrimeFactor_badPrimeAffineExample {c : ℤ} (hc : c ≠ 0) :
    literalAffineBadPrimeFactor (badPrimeAffineExample c) = 1 := by
  have hirr (K : Type) [Field K] :
      Irreducible (map (Int.castRingHom K) (badPrimeAffineExample c)) := by
    rw [map_badPrimeAffineExample]
    exact irreducible_C_mul_X_sq_add_X _
  rw [literalAffineBadPrimeFactor_eq_exp _ (hirr _) (totalDegree_badPrimeAffineExample hc) ∅]
  · simp
  · intro p
    simp [LiteralAffineBadReduction, hirr]

/-- The homogenization `c x₁² + x₀ x₂` has bad reduction exactly at the prime factors of `c`. -/
lemma literalAffineBadReduction_badPrimeHomogenizedExample (c : ℤ) (p : ℕ) :
    LiteralAffineBadReduction (badPrimeHomogenizedExample c) p ↔ p.Prime ∧ (p : ℤ) ∣ c := by
  unfold LiteralAffineBadReduction
  refine ⟨fun ⟨hp, h⟩ => ⟨hp, ?_⟩, fun ⟨hp, hpc⟩ => ⟨hp, ?_⟩⟩
  · let : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    by_contra hne
    apply h
    rw [map_badPrimeHomogenizedExample]
    apply irreducible_C_mul_X_sq_add_X_mul_X
    rwa [← map_intCast (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))),
      map_ne_zero_iff _ (algebraMap (ZMod p) _).injective]
  · let : Fact p.Prime := ⟨hp⟩
    have hc : (c : AlgebraicClosure (ZMod p)) = 0 := by
      rw [← map_intCast (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))),
        (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hpc, map_zero]
    dsimp only
    rw [map_badPrimeHomogenizedExample, hc, map_zero, zero_mul, zero_add]
    intro h
    rcases h.isUnit_or_isUnit rfl with h0 | h2
    · exact X_prime.not_isUnit h0
    · exact X_prime.not_isUnit h2

/-- `b(F₁)` is the factor of the prime divisors of `c` above `27 · 2⁴ = 432`. -/
theorem literalAffineBadPrimeFactor_badPrimeHomogenizedExample {c : ℤ} (hc : c ≠ 0) :
    literalAffineBadPrimeFactor (badPrimeHomogenizedExample c) =
      primeSetFactor (c.natAbs.primeFactors.filter (432 < ·)) := by
  have hirr : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ))
      (badPrimeHomogenizedExample c)) := by
    rw [map_badPrimeHomogenizedExample]
    exact irreducible_C_mul_X_sq_add_X_mul_X (Int.cast_ne_zero.mpr hc)
  apply literalAffineBadPrimeFactor_eq_exp _ hirr (totalDegree_badPrimeHomogenizedExample hc)
  intro p
  rw [literalAffineBadReduction_badPrimeHomogenizedExample, Finset.mem_filter,
    Nat.mem_primeFactors, Int.natCast_dvd]
  have : stepanovThreshold 2 = 432 := by norm_num [stepanovThreshold]
  have hc' := Int.natAbs_ne_zero.mpr hc
  rw [this]
  tauto

/-- For `c = 439`, `b(f) = 1` but `b(F₁) = 439^(1/439) > 1`. -/
theorem literalAffineBadPrimeFactor_homogenization_ne :
    literalAffineBadPrimeFactor (badPrimeAffineExample 439) = 1 ∧
      literalAffineBadPrimeFactor (badPrimeHomogenizedExample 439) = (439 : ℝ) ^ (1 / 439 : ℝ) ∧
      1 < literalAffineBadPrimeFactor (badPrimeHomogenizedExample 439) := by
  have h439 : Nat.Prime 439 := by norm_num
  have hb : literalAffineBadPrimeFactor (badPrimeHomogenizedExample 439) =
      (439 : ℝ) ^ (1 / 439 : ℝ) := by
    rw [literalAffineBadPrimeFactor_badPrimeHomogenizedExample (by norm_num),
      show (439 : ℤ).natAbs = 439 from rfl, h439.primeFactors, Finset.filter_singleton,
      Real.rpow_def_of_pos (by norm_num)]
    norm_num [div_eq_mul_inv]
  refine ⟨literalAffineBadPrimeFactor_badPrimeAffineExample (by norm_num), hb, ?_⟩
  rw [hb]
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

/-- The ratio `b(F₁) / b(f)` is unbounded. -/
theorem literalAffineBadPrimeFactor_homogenization_unbounded (M : ℝ) :
    ∃ c : ℤ, c ≠ 0 ∧ literalAffineBadPrimeFactor (badPrimeAffineExample c) = 1 ∧
      M < literalAffineBadPrimeFactor (badPrimeHomogenizedExample c) := by
  let small := ∑ p ∈ Finset.range 433, Real.log p / p
  have hsmall : 0 ≤ small :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  let x := Real.exp (max M 0 + mertensError + small)
  have hx : 1 ≤ x :=
    Real.one_le_exp (by linarith [le_max_right M 0, mertensError_pos])
  let S := ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ Finset.range 433
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  refine ⟨(∏ p ∈ S, p : ℕ), by exact_mod_cast hpos.ne', ?_, ?_⟩
  · exact literalAffineBadPrimeFactor_badPrimeAffineExample (by exact_mod_cast hpos.ne')
  · rw [literalAffineBadPrimeFactor_badPrimeHomogenizedExample (by exact_mod_cast hpos.ne'),
      Int.natAbs_natCast, Nat.primeFactors_prod hS,
      Finset.filter_true_of_mem fun p hp => by
        have := (Finset.mem_sdiff.mp hp).2
        simp only [Finset.mem_range, not_lt] at this
        omega]
    have hsum := prime_sum_lower_sdiff hx (Finset.range 433)
    rw [Real.log_exp] at hsum
    have := Real.add_one_le_exp (∑ p ∈ S, Real.log p / p)
    change _ < Real.exp _
    linarith [le_max_left M 0]

end
end CCDN
