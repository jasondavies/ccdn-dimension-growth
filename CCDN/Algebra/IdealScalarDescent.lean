/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.HilbertScalarExtension
public import CCDN.Algebra.LowDegreePointSeparation
/-! Coefficient-linear descent detects nonmembership in scalar-extended
ideals, and descends degree-bounded separating equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientLinearPolynomial_sub {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f g : MvPolynomial (Fin n) L) :
    coefficientLinearPolynomial φ (f - g) =
      coefficientLinearPolynomial φ f - coefficientLinearPolynomial φ g := by
  ext a
  simp [coefficientLinearPolynomial_coeff]

lemma coefficientLinearPolynomial_map_of_one {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (hφ : φ 1 = 1) (f : MvPolynomial (Fin n) K) :
    coefficientLinearPolynomial φ (map (algebraMap K L) f) = f := by
  ext a
  rw [coefficientLinearPolynomial_coeff, coeff_map]
  have hh := φ.map_smul (f.coeff a) (1 : L)
  simpa only [Algebra.smul_def, mul_one, hφ, Algebra.algebraMap_self,
    RingHom.id_apply] using hh

theorem mem_ideal_scalar_extension_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) K) :
    map (algebraMap K L) f ∈ I.map (map (algebraMap K L)) ↔ f ∈ I := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
    have hh := coefficientLinearPolynomial_mem_scalar_extension I _ h φ
    rwa [coefficientLinearPolynomial_map_of_one φ hφ] at hh
  · exact Ideal.mem_map_of_mem _

/-- Some coefficient functional detects nonmembership in an extended ideal. -/
theorem exists_coefficientLinearPolynomial_not_mem
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin n) L)
    (hg : g ∉ J.map (map (algebraMap K L))) :
    ∃ φ : L →ₗ[K] K, coefficientLinearPolynomial φ g ∉ J := by
  classical
  let J' := J.map (map (algebraMap K L))
  obtain ⟨r, hrstd, _, hrJ⟩ := Ideal.exists_standard_representative_degLex J' g
  have hr0 : r ≠ 0 := by intro h; exact hg (by simpa only [h, sub_zero] using hrJ)
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero hr0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K ha
  refine ⟨φ, ?_⟩
  intro hgJ
  have hdJ := coefficientLinearPolynomial_mem_scalar_extension J (g - r) hrJ φ
  rw [coefficientLinearPolynomial_sub] at hdJ
  have hrmem : coefficientLinearPolynomial φ r ∈ J := by
    have hh := J.sub_mem hgJ hdJ
    simpa only [sub_sub_cancel] using hh
  have hrstdK : coefficientLinearPolynomial φ r ∈
      restrictSupport K (Ideal.standardExponents J MonomialOrder.degLex) := by
    intro b hb
    have hbr : b ∈ r.support := by
      change b ∈ (coefficientLinearPolynomial φ r).support at hb
      rw [mem_support_iff] at hb ⊢
      intro hzero
      apply hb
      rw [coefficientLinearPolynomial_coeff, hzero, map_zero]
    have hh := hrstd hbr
    simpa only [J', standardExponents_scalar_extension] using hh
  have hrzero := Ideal.eq_zero_of_mem_restrictSupport_standardExponents J MonomialOrder.degLex hrstdK hrmem
  have hc := coefficientLinearPolynomial_coeff φ r a
  have hz : φ (r.coeff a) = 0 := by simpa [hrzero] using hc.symm
  exact hφ hz

end
end CCDN
