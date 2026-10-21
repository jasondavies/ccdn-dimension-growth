/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.LiteralAffineBadPrimes
public import CCDN.Auxiliary.ScaledHypersurfaceBadPrimes
public import CCDN.Noether.GenericPlaneStretch
public import CCDN.Determinant.AffineCongruenceDeterminant
/-! Primitivity and good affine reductions for prime-scaled models, with
no degree-preservation requirement modulo the good primes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma variableScaleEquiv_monomial {K σ : Type*} [Field K]
    (a : K) (ha : a ≠ 0) (m : σ →₀ ℕ) (c : K) :
    variableScaleEquiv K σ a ha (monomial m c) = monomial m (a ^ m.degree * c) := by
  classical
  rw [monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow,
    variableScaleEquiv_X, mul_pow, Finsupp.prod_mul]
  have hpow : (m.prod fun _ e => (C a : MvPolynomial σ K) ^ e) = C a ^ m.degree := by
    change (∏ i ∈ m.support, (C a : MvPolynomial σ K) ^ m i) = C a ^ (∑ i ∈ m.support, m i)
    rw [Finset.prod_pow_eq_pow_sum]
  rw [show variableScaleEquiv K σ a ha (C c) = C c from
    (variableScaleEquiv K σ a ha).commutes c, hpow, ← map_pow,
    ← mul_assoc, ← map_mul, mul_comm c]
  exact monomial_eq.symm

lemma affineChart_scaledHomogenize_eq_variableScale {K : Type*} [Field K] {n : ℕ}
    (d : ℕ) (h : K) (hh : h ≠ 0) (f : MvPolynomial (Fin n) K) :
    affineChart n (scaledHomogenize d h f) = variableScaleEquiv K (Fin n) h hh f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [affineChart_monomial, chartExponent_homogenizedExponent,
    variableScaleEquiv_monomial]
  rfl

lemma affineChart_scaledHomogenize_map_irreducible {K : Type*} [Field K] {n d : ℕ}
    (φ : ℤ →+* K) (h : ℤ) (hh : φ h ≠ 0) (f : MvPolynomial (Fin n) ℤ) :
    Irreducible (map φ (affineChart n (scaledHomogenize d h f))) ↔ Irreducible (map φ f) := by
  rw [← affineChart_map, scaledHomogenize_map,
    affineChart_scaledHomogenize_eq_variableScale d (φ h) hh]
  exact MulEquiv.irreducible_iff (f := variableScaleEquiv K (Fin n) (φ h) hh)

lemma prime_scaled_zero_primitive {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (x : IntPoint n) (hx : eval x f = 0) :
    Finset.univ.gcd (Fin.cons (p : ℤ) x) = 1 := by
  classical
  rw [← Finset.normalize_gcd, normalize_eq_one, Int.isUnit_iff_natAbs_eq]
  by_contra hn
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hn
  have hqdiv : (q : ℤ) ∣ Finset.univ.gcd (Fin.cons (p : ℤ) x) := Int.natCast_dvd.mpr hqg
  have hqp : (q : ℤ) ∣ p := hqdiv.trans (Finset.gcd_dvd (Finset.mem_univ 0))
  have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast hqp)
  subst q
  have hpx (j) : (p : ℤ) ∣ x j := hqdiv.trans (Finset.gcd_dvd (Finset.mem_univ j.succ))
  have he := dvd_eval_sub_of_dvd_coordinates (p : ℤ) x (0 : Fin n → ℤ)
    (fun j => by simpa using hpx j) f
  rw [hx, eval_zero, constantCoeff_eq, zero_sub] at he
  exact hp0 (dvd_neg.mp he)

end
end CCDN
