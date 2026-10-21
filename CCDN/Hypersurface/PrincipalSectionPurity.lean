/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Hilbert.PrincipalHilbertPolynomial
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Projection.LinearNormalizationInfinite
import CCDN.ForMathlib.KrullHeight
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
/-! Principal sections of affine prime varieties are pure dimensional.
A linear normalization is constructed from the Hilbert dimension.
Going down contracts each section component to a height-one prime in the
polynomial normalization ring; its principal quotient has dimension one less. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem principal_section_minimalPrime_hilbert_dimension
    {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial (Fin n) K) (hf : f ∉ I)
    (P : Ideal (MvPolynomial (Fin n) K))
    (hP : P ∈ (I ⊔ Ideal.span {f}).minimalPrimes) :
    (filteredHilbertPolynomial P).natDegree = m := by
  classical
  have : P.IsPrime := hP.isPrime
  have hIP : I ≤ P := le_sup_left.trans hP.le
  have hfP : f ∈ P := hP.le ((show Ideal.span {f} ≤ I ⊔ Ideal.span {f}
    from le_sup_right) (Ideal.subset_span (Set.mem_singleton f)))
  have hmn : m + 1 ≤ n := by
    obtain ⟨_, _, hd, _⟩ := filteredHilbertPolynomial_positive_multiplicity I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›)
    simpa only [hdim, Fintype.card_fin] using hd
  obtain ⟨l, _, hint, hinj⟩ := exists_linear_integral_normalization_infinite_of_le m n hmn I hdim
  let R := MvPolynomial (Fin (m + 1)) K
  let A := MvPolynomial (Fin n) K ⧸ I
  let ψ : R →ₐ[K] A := projectionCoordinateMap I l
  let : Algebra R A := ψ.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hint⟩
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  let Q : Ideal A := P.map (Ideal.Quotient.mk I)
  have : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIP)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have hqf : Ideal.Quotient.mk I f ∈ Q := Ideal.mem_map_of_mem _ hfP
    rw [h, Ideal.mem_bot] at hqf
    exact hf (Ideal.Quotient.eq_zero_iff_mem.mp hqf)
  have hQheight : Q.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hP
  let J := Q.under R
  have hJheight : J.height = 1 := Ideal.height_under_eq_one_of_height_le_one R A Q hQ0 hQheight
  let : J.IsPrincipal := Ideal.isPrincipal_under_of_height_le_one R A Q hQ0 hQheight
  let F : R := Submodule.IsPrincipal.generator J
  have hFspan : Ideal.span {F} = J := Ideal.span_singleton_generator J
  have hF0 : F ≠ 0 := by
    intro h
    have hJ0 : J = ⊥ := by rw [← hFspan, h]; simp
    exact (Ideal.ne_bot_of_height_eq_one hJheight) hJ0
  have hFdeg : 0 < F.totalDegree := by
    by_contra! h
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hc : F.coeff 0 ≠ 0 := by
      intro hc
      apply hF0
      rw [he, hc, map_zero]
    have hunit : IsUnit F := by
      rw [he]
      exact (isUnit_iff_ne_zero.mpr hc).map C
    exact (Ideal.IsPrime.ne_top (inferInstance : J.IsPrime))
      (hFspan.symm.trans (Ideal.span_singleton_eq_top.mpr hunit))
  let φ : A →ₐ[K] MvPolynomial (Fin n) K ⧸ P :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K P)
      (fun g hg => Ideal.Quotient.eq_zero_iff_mem.mpr (hIP hg))
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk I g, rfl⟩
  have hcomp : φ.comp ψ = projectionCoordinateMap P l := by
    ext i
    simp only [AlgHom.comp_apply, ψ, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  have hintP : (projectionCoordinateMap P l).IsIntegral := by
    have hh := RingHom.IsIntegral.trans ψ.toRingHom φ.toRingHom hint
      (RingHom.isIntegral_of_surjective _ hφsurj)
    change (φ.comp ψ).IsIntegral at hh
    rwa [hcomp] at hh
  have hQcomap : Q.comap (Ideal.Quotient.mk I) = P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hker : RingHom.ker (projectionCoordinateMap P l) = J := by
    ext g
    change Ideal.Quotient.mk P ((aeval l) g) = 0 ↔
      Ideal.Quotient.mk I ((aeval l) g) ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (aeval l) g ∈ P ↔ (aeval l) g ∈ Q.comap (Ideal.Quotient.mk I)
    rw [hQcomap]
  have he := integral_projection_hilbert_dimension_eq P (projectionCoordinateMap P l) hintP
  rw [hker, ← hFspan] at he
  exact he.symm.trans (principal_filteredHilbertPolynomial_natDegree F hF0 hFdeg)

theorem principal_section_minimalPrimeComponents_pure
    {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial (Fin n) K) (hf : f ∉ I) :
    ∀ P : minimalPrimeComponents (I ⊔ Ideal.span {f}),
      (filteredHilbertPolynomial P.val).natDegree = m :=
  fun P => principal_section_minimalPrime_hilbert_dimension I hdim f hf P.val
    (mem_minimalPrimeComponents.mp P.property)

end
end CCDN
