/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.Noether.GenericPlaneStretch
public import CCDN.Algebra.ScaledHomogenization
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Determinant.ProjectiveLocalDeterminant

/-!
# The literal affine bad-prime factor

`literalAffineBadPrimeFactor f` is the factor `b(f)` of CCDN Definition 3.2.1 applied verbatim
to an affine integer polynomial `f`: it sums `log p / p` over the primes `p > 27 d⁴` at which the
reduction of `f` is not absolutely irreducible (`LiteralAffineBadReduction`). A reduction that
loses degree but remains absolutely irreducible is good, so primes at which `f` drops degree are
not counted.

This is in contrast with `hypersurfaceBadPrimeFactor` (`HypersurfaceBadReduction`), which also
counts primes at which the degree drops, and is the factor used for homogeneous equations; the
literal factor is at most it (`literalAffineBadPrimeFactor_le_inclusive`). The printed proof of
Proposition 4.2.1 passes to the homogenization `F₁` of `f` and uses `b(F₁) = b(f)`, which fails
(`Counterexample/HomogenizedBadPrimeFactor.lean`). The `LiteralAffine*` modules therefore prove
Proposition 4.2.1 and Corollary 4.2.4 with the literal factor, working in the affine chart.

The module also proves primitivity and good affine reductions for prime-scaled models, with no
degree-preservation requirement modulo the good primes, since the literal factor does not count
primes at which the degree drops.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def LiteralAffineBadReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    ¬ Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

private lemma LiteralAffineBadReduction.hypersurfaceBadReduction {σ : Type*}
    {f : MvPolynomial σ ℤ} {p : ℕ} (h : LiteralAffineBadReduction f p) :
    HypersurfaceBadReduction f p := ⟨h.1, Or.inr h.2⟩

lemma finite_literal_affine_bad_primes {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f) :
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ LiteralAffineBadReduction f p}.Finite := by
  apply (finite_fin_hypersurface_bad_primes f hf
    (absolute_integer_polynomial_totalDegree_pos f hf)).subset
  intro p hp
  exact ⟨hp.1, hp.2.hypersurfaceBadReduction⟩

/-- The literal affine bad-prime factor of CCDN Definition 3.2.1: `badPrimeFactor` for
`LiteralAffineBadReduction`, which counts only failure of absolute irreducibility. -/
def literalAffineBadPrimeFactor {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) : ℝ :=
  badPrimeFactor LiteralAffineBadReduction finite_literal_affine_bad_primes f

lemma literalAffineBadPrimeFactor_nonneg {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    0 ≤ literalAffineBadPrimeFactor f :=
  badPrimeFactor_nonneg f

lemma literalAffineBadPrimeFactor_eq_zero {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : ¬AbsolutelyIrreducible f) :
    literalAffineBadPrimeFactor f = 0 :=
  badPrimeFactor_eq_zero hf

lemma literalAffineBadPrimeFactor_eq_exp {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : AbsolutelyIrreducible f)
    (hd : f.totalDegree = d) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ LiteralAffineBadReduction f p) :
    literalAffineBadPrimeFactor f = primeSetFactor bad :=
  badPrimeFactor_eq_primeSetFactor hf hd bad hbad

lemma literalAffineBadPrimeFactor_le_inclusive {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    literalAffineBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor f :=
  badPrimeFactor_mono f fun _ h => h.hypersurfaceBadReduction

private lemma literalAffineBadReduction_affineTranslation {n : ℕ}
    (a : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ) (p : ℕ) :
    LiteralAffineBadReduction (affineTranslation ℤ a f) p ↔ LiteralAffineBadReduction f p := by
  unfold LiteralAffineBadReduction
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  rw [affineTranslation_map, affineTranslation_irreducible_iff]

theorem literalAffineBadPrimeFactor_affineTranslation {n : ℕ}
    (a : Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    literalAffineBadPrimeFactor (affineTranslation ℤ a f) = literalAffineBadPrimeFactor f := by
  classical
  have hir : AbsolutelyIrreducible (affineTranslation ℤ a f) ↔ AbsolutelyIrreducible f := by
    dsimp only [AbsolutelyIrreducible]
    rw [affineTranslation_map, affineTranslation_irreducible_iff]
  by_cases hf : AbsolutelyIrreducible f
  · let bad := (finite_literal_affine_bad_primes f hf).toFinset
    have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
        LiteralAffineBadReduction f p := by
      simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [literalAffineBadPrimeFactor_eq_exp f hf rfl bad hbad]
    exact literalAffineBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad (by intro p; rw [hbad, literalAffineBadReduction_affineTranslation])
  · rw [literalAffineBadPrimeFactor_eq_zero f hf,
      literalAffineBadPrimeFactor_eq_zero _ (fun h => hf (hir.mp h))]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma variableScaleEquiv_monomial {K σ : Type*} [Field K]
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

private lemma affineChart_scaledHomogenize_eq_variableScale {K : Type*} [Field K] {n : ℕ}
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
