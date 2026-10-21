/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalHomogeneousForm
public import CCDN.Algebra.CoefficientwiseHomogeneous
/-! Homogeneous substitution with independent coefficient and polynomial
variables, and specialization of the resulting coefficient forms. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finsupp

namespace CoefficientwiseHomogeneous

private lemma pow {R σ τ : Type*} [CommRing R]
    {f : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ}
    (hf : CoefficientwiseHomogeneous f d) (n : ℕ) :
    CoefficientwiseHomogeneous (f ^ n) (d * n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.mul_zero] using one (R := R) (σ := σ) (τ := τ)
  | succ n ih => simpa only [pow_succ, Nat.mul_succ] using ih.mul hf

lemma eval₂ {R S σ τ υ : Type*} [CommRing R] [CommRing S]
    {φ : MvPolynomial σ R} {m n : ℕ} (hφ : φ.IsHomogeneous m)
    (f : R →+* MvPolynomial τ (MvPolynomial υ S))
    (g : σ → MvPolynomial τ (MvPolynomial υ S))
    (hf : ∀ r, CoefficientwiseHomogeneous (f r) 0)
    (hg : ∀ i, CoefficientwiseHomogeneous (g i) n) :
    CoefficientwiseHomogeneous (MvPolynomial.eval₂ f g φ) (n * m) := by
  apply CoefficientwiseHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply CoefficientwiseHomogeneous.mul (hf _) _
  convert! CoefficientwiseHomogeneous.prod _ _ (fun k => n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum, ← hφ hi, weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  · intro k _
    exact (hg k).pow _

end CoefficientwiseHomogeneous

lemma homogeneousCoefficientSpecialization_map {R S σ : Type*}
    [CommRing R] [CommRing S] [Fintype σ] [DecidableEq σ]
    (ψ : R →+* S) (d : ℕ) (f : MvPolynomial σ R)
    (Φ : MvPolynomial (Sym σ d) ℤ) :
    ψ (homogeneousCoefficientSpecialization d f Φ) =
      homogeneousCoefficientSpecialization d (map ψ f) Φ := by
  have he : ψ.comp (homogeneousCoefficientSpecialization d f) =
      homogeneousCoefficientSpecialization d (map ψ f) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [homogeneousCoefficientSpecialization]
    · intro i
      simp [homogeneousCoefficientSpecialization, homogeneousCoefficientData, coeff_map]
  exact RingHom.congr_fun he Φ

lemma homogeneousCoefficientSpecialization_homogeneous
    {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    (d e r : ℕ) (f : MvPolynomial σ (MvPolynomial τ ℤ))
    (hf : CoefficientwiseHomogeneous f e)
    (Φ : MvPolynomial (Sym σ d) ℤ) (hΦ : Φ.IsHomogeneous r) :
    (homogeneousCoefficientSpecialization d f Φ).IsHomogeneous (e * r) := by
  apply hΦ.eval₂
  · intro z
    simpa using isHomogeneous_C τ z
  · intro i
    exact hf (homogeneousCoefficientExponent σ d i)

end
end CCDN
