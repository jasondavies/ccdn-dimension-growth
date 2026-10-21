/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.StandardExponents
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
/-! Galois-stable polynomial ideals descend to the fixed field. Standard
monomial representatives of individual monomials construct fixed ideal
generators. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem standard_representative_fixed_by_coefficientEquiv
    {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (e : K ≃+* K)
    (hI : I.map (mapEquiv (Fin n) e) = I)
    (f r : MvPolynomial (Fin n) K) (hf : mapEquiv (Fin n) e f = f)
    (hr : r ∈ restrictSupport K (Ideal.standardExponents I MonomialOrder.degLex))
    (hfr : f - r ∈ I) :
    mapEquiv (Fin n) e r = r := by
  have hmr : mapEquiv (Fin n) e r ∈
      restrictSupport K (Ideal.standardExponents I MonomialOrder.degLex) := by
    intro a ha
    apply hr
    change a ∈ r.support
    change a ∈ (mapEquiv (Fin n) e r).support at ha
    rw [mapEquiv_apply, support_map_of_injective r
      (show Function.Injective (e : K →+* K) from e.injective)] at ha
    exact ha
  have hfm : f - mapEquiv (Fin n) e r ∈ I := by
    have hh := Ideal.mem_map_of_mem (mapEquiv (Fin n) e) hfr
    rwa [hI, map_sub, hf] at hh
  apply sub_eq_zero.mp
  apply Ideal.eq_zero_of_mem_restrictSupport_standardExponents I MonomialOrder.degLex
  · exact Submodule.sub_mem _ hmr hr
  · have hh := I.sub_mem hfr hfm
    simpa only [sub_sub_sub_cancel_left] using hh

/-- Every Galois-stable ideal is the scalar extension of its contraction.
The extension may be infinite. -/
theorem galois_stable_polynomial_ideal_descends
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (hstable : ∀ γ : Gal(K/k), I.map (map γ.toRingHom) = I) :
    (I.comap (map (algebraMap k K))).map (map (algebraMap k K)) = I := by
  classical
  let J := (I.comap (map (algebraMap k K))).map (map (algebraMap k K))
  refine le_antisymm Ideal.map_comap_le ?_
  intro f hf
  choose r hrstd hrdeg hrI using fun a : Fin n →₀ ℕ =>
    Ideal.exists_standard_representative_degLex I (monomial a 1)
  have hfix (a : Fin n →₀ ℕ) (γ : Gal(K/k)) :
      map γ.toRingHom (monomial a 1 - r a) = monomial a 1 - r a := by
    have hγ : I.map (mapEquiv (Fin n) γ.toRingEquiv) = I := hstable γ
    have hh := standard_representative_fixed_by_coefficientEquiv I γ.toRingEquiv
      hγ (monomial a 1) (r a) (by simp) (hrstd a) (hrI a)
    simpa [mapEquiv_apply] using hh
  have hgen (a : Fin n →₀ ℕ) : monomial a 1 - r a ∈ J := by
    have hcoeff : ∀ c ∈ (monomial a 1 - r a).coeffs,
        c ∈ Set.range (algebraMap k K) := by
      intro c hc
      obtain ⟨b, _, rfl⟩ := mem_coeffs_iff.mp hc
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro γ
      have hh := congrArg (fun p : MvPolynomial (Fin n) K => p.coeff b) (hfix a γ)
      simpa only [coeff_map, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv] using hh
    obtain ⟨g, hg⟩ := mem_range_map_iff_coeffs_subset.mpr hcoeff
    rw [← hg]
    apply Ideal.mem_map_of_mem
    change map (algebraMap k K) g ∈ I
    rw [hg]
    exact hrI a
  let q : MvPolynomial (Fin n) K :=
    ∑ a ∈ f.support, C (f.coeff a) * (monomial a 1 - r a)
  have hq : q ∈ J := by
    apply J.sum_mem
    intro a _
    exact J.mul_mem_left _ (hgen a)
  have hqI : q ∈ I := Ideal.map_comap_le hq
  have hrepr : f - q = ∑ a ∈ f.support, (f.coeff a) • r a := by
    dsimp only [q]
    simp only [mul_sub, Finset.sum_sub_distrib, C_mul_monomial, mul_one,
      smul_eq_C_mul]
    rw [support_sum_monomial_coeff]
    abel
  have hrmem : f - q ∈ restrictSupport K (Ideal.standardExponents I MonomialOrder.degLex) := by
    rw [hrepr]
    apply Submodule.sum_mem
    intro a _
    exact Submodule.smul_mem _ _ (hrstd a)
  have heq : f = q := sub_eq_zero.mp
    (Ideal.eq_zero_of_mem_restrictSupport_standardExponents I MonomialOrder.degLex hrmem (I.sub_mem hf hqI))
  rw [heq]
  exact hq

/-- A prime component over a Galois extension that does not descend is
moved by a coefficient automorphism. -/
theorem exists_galois_moving_polynomial_ideal
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (hne : (I.comap (map (algebraMap k K))).map (map (algebraMap k K)) ≠ I) :
    ∃ γ : Gal(K/k), I.map (map γ.toRingHom) ≠ I := by
  by_contra! h
  exact hne (galois_stable_polynomial_ideal_descends k K I h)

end
end CCDN
