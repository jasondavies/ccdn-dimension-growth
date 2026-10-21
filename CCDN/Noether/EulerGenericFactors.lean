/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerFactorKernel
public import CCDN.Noether.EulerUniversalForms
public import Mathlib.Tactic.Continuity
import CCDN.Noether.EulerPairBasisValues
import CCDN.Projection.ShearNormalization

/-! Generic factors with independent integral coefficient parameters.
Specializing the logarithmic pair at `(x^a,1)` proves that the generic
pair is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

def eulerPolynomialFromCoefficients {R : Type*} [CommRing R]
    (d : ℕ) (c : EulerLowIndex d → R) : R[X][X] :=
  ∑ i, c i • eulerCoefficientMonomial R d i

lemma eulerPolynomialFromCoefficients_degree {R : Type*} [CommRing R]
    (d : ℕ) (c : EulerLowIndex d → R) :
    bivariateTotalDegree (eulerPolynomialFromCoefficients d c) ≤ d := by
  classical
  let u : MvPolynomial.restrictTotalDegree (Fin 2) R d :=
    ∑ i, c i • eulerLowBasis R d i
  have he : eulerPolynomialFromCoefficients d c = bivariatePolynomialEquiv R u.val := by
    simp only [u, Submodule.coe_sum, SetLike.val_smul, map_sum, map_smul,
      eulerLowBasis_apply, eulerCoefficientMonomial, eulerPolynomialFromCoefficients]
  rw [he]
  change ((bivariatePolynomialEquiv R).symm (bivariatePolynomialEquiv R u.val)).totalDegree ≤ _
  rw [AlgEquiv.symm_apply_apply]
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp u.property

lemma eulerPolynomialFromCoefficients_data {R : Type*} [CommRing R]
    (d : ℕ) (f : R[X][X]) (hf : bivariateTotalDegree f ≤ d) :
    eulerPolynomialFromCoefficients d (eulerCoefficientData d f) = f :=
  eulerCoefficientData_reconstruct d f hf

lemma bivariateMap_smul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (f : R[X][X]) :
    bivariateMap φ (a • f) = φ a • bivariateMap φ f := by
  simp [bivariate_smul_eq_constant_mul, bivariateMap]

lemma eulerPolynomialFromCoefficients_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (c : EulerLowIndex d → R) :
    bivariateMap φ (eulerPolynomialFromCoefficients d c) =
      eulerPolynomialFromCoefficients d (φ ∘ c) := by
  simp only [eulerPolynomialFromCoefficients, map_sum, bivariateMap_smul,
    eulerCoefficientMonomial_map, Function.comp_apply]

abbrev EulerFactorParameters (a b : ℕ) := EulerLowIndex a ⊕ EulerLowIndex b

def genericEulerFactorLeft (a b : ℕ) :
    (MvPolynomial (EulerFactorParameters a b) ℤ)[X][X] :=
  eulerPolynomialFromCoefficients a (fun i => MvPolynomial.X (Sum.inl i))

def genericEulerFactorRight (a b : ℕ) :
    (MvPolynomial (EulerFactorParameters a b) ℤ)[X][X] :=
  eulerPolynomialFromCoefficients b (fun i => MvPolynomial.X (Sum.inr i))

def genericEulerFactorSpecialization {R : Type*} [CommRing R] (a b : ℕ)
    (g h : R[X][X]) : MvPolynomial (EulerFactorParameters a b) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (eulerCoefficientData a g) (eulerCoefficientData b h))

lemma genericEulerFactorLeft_specialize {R : Type*} [CommRing R]
    (a b : ℕ) (g h : R[X][X]) (hg : bivariateTotalDegree g ≤ a) :
    bivariateMap (genericEulerFactorSpecialization a b g h) (genericEulerFactorLeft a b) = g := by
  rw [genericEulerFactorLeft, eulerPolynomialFromCoefficients_map]
  have he : (genericEulerFactorSpecialization a b g h) ∘
      (fun i : EulerLowIndex a => MvPolynomial.X (Sum.inl i)) = eulerCoefficientData a g := by
    funext i
    exact MvPolynomial.eval₂_X _ _ _
  rw [he]
  exact eulerPolynomialFromCoefficients_data a g hg

lemma genericEulerFactorRight_specialize {R : Type*} [CommRing R]
    (a b : ℕ) (g h : R[X][X]) (hh : bivariateTotalDegree h ≤ b) :
    bivariateMap (genericEulerFactorSpecialization a b g h) (genericEulerFactorRight a b) = h := by
  rw [genericEulerFactorRight, eulerPolynomialFromCoefficients_map]
  have he : (genericEulerFactorSpecialization a b g h) ∘
      (fun i : EulerLowIndex b => MvPolynomial.X (Sum.inr i)) = eulerCoefficientData b h := by
    funext i
    exact MvPolynomial.eval₂_X _ _ _
  rw [he]
  exact eulerPolynomialFromCoefficients_data b h hh

lemma eulerFactorPair_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a b : ℕ) (g h : R[X][X]) :
    (bivariateMap φ (eulerFactorPair a b g h).1,
      bivariateMap φ (eulerFactorPair a b g h).2) =
      eulerFactorPair a b (bivariateMap φ g) (bivariateMap φ h) := by
  simp only [eulerFactorPair, map_sub, bivariateMap_smul, map_natCast, map_mul,
    bivariateMap_derivative, bivariateMap_coefficientDerivative]

lemma bivariateTotalDegree_outer_X_pow {R : Type*} [CommRing R] [Nontrivial R] (a : ℕ) :
    bivariateTotalDegree (X ^ a : R[X][X]) = a := by
  have he := bivariatePolynomialEquiv_X_zero (R := R)
  rw [← he, ← map_pow]
  change ((bivariatePolynomialEquiv R).symm
    (bivariatePolynomialEquiv R (MvPolynomial.X 0 ^ a))).totalDegree = _
  rw [AlgEquiv.symm_apply_apply, MvPolynomial.totalDegree_X_pow]

lemma eulerFactorPair_outer_power_one_ne_zero (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    eulerFactorPair a b (X ^ a : ℚ[X][X]) 1 ≠ 0 := by
  intro hh
  have hfst := congrArg Prod.fst hh
  change (b : ℚ) • (1 * (X ^ a : ℚ[X][X]).derivative) -
    (a : ℚ) • (X ^ a * (1 : ℚ[X][X]).derivative) = 0 at hfst
  simp only [one_mul, derivative_one, mul_zero, smul_zero, sub_zero] at hfst
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0 : (X ^ a : ℚ[X][X]).derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    simpa only [natDegree_X_pow] using (Nat.ne_of_gt ha)
  exact (smul_ne_zero hb0 hd0) hfst

/-- The generic logarithmic pair is nonzero over its integral coefficient
ring, proved by a rational specialization. -/
theorem genericEulerFactorPair_ne_zero (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    eulerFactorPair a b (genericEulerFactorLeft a b) (genericEulerFactorRight a b) ≠ 0 := by
  intro hz
  let φ := genericEulerFactorSpecialization a b (X ^ a : ℚ[X][X]) 1
  have he := eulerFactorPair_map φ a b (genericEulerFactorLeft a b) (genericEulerFactorRight a b)
  have hg : bivariateTotalDegree (X ^ a : ℚ[X][X]) ≤ a :=
    (bivariateTotalDegree_outer_X_pow a).le
  have hh : bivariateTotalDegree (1 : ℚ[X][X]) ≤ b := by
    simp only [bivariateTotalDegree, map_one, MvPolynomial.totalDegree_one]
    omega
  rw [genericEulerFactorLeft_specialize a b _ _ hg,
    genericEulerFactorRight_specialize a b _ _ hh] at he
  rw [hz] at he
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero] at he
  exact eulerFactorPair_outer_power_one_ne_zero a b ha hb he.symm

end
end CCDN
