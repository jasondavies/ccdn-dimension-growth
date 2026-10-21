/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceHilbert
import CCDN.ForMathlib.LinearMap
import CCDN.ForMathlib.MvPolynomial
import CCDNPaper.Determinant.InitialFormMultiplication
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The exact Hilbert function of the origin-adic layers of an
arbitrary hypersurface. Initial-form cancellation identifies the entire
homogeneous kernel, not merely a subspace of relations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ : Type*} [Field K]

private lemma homogeneous_mem_originTruncation_iff
    {f g : MvPolynomial σ K} {μ k : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ) (hμ : homogeneousComponent μ f ≠ 0)
    (hk : μ ≤ k) (hg : g.IsHomogeneous k) :
    g ∈ originTruncationIdeal f k ↔
      ∃ u : MvPolynomial σ K, u.IsHomogeneous (k - μ) ∧
        homogeneousComponent μ f * u = g := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have hfu : f * u ∈ idealOfVars σ K ^ k := by
      have h := (idealOfVars σ K ^ k).sub_mem (homogeneous_mem_origin_power hg)
        (Ideal.pow_le_pow_right (Nat.le_succ k) hb)
      simpa only [← hab, add_sub_cancel_right] using h
    have hu := origin_power_cancel_initial_form hf hμ hfu
    refine ⟨homogeneousComponent (k - μ) u, homogeneousComponent_isHomogeneous _ _, ?_⟩
    have hh := congrArg (homogeneousComponent k) hab
    rw [map_add, homogeneousComponent_eq_zero_of_mem_origin_power hb (Nat.lt_succ_self k),
      add_zero, homogeneousComponent_eq_self hg] at hh
    rwa [← Nat.add_sub_of_le hk, first_homogeneousComponent_mul hf hu] at hh
  · rintro ⟨u, hu, rfl⟩
    exact initial_form_multiple_mem_truncation hf hk hu

/-- Exact rank-nullity for the homogeneous truncation map. -/
private theorem originLayer_hilbert_eq [Finite σ]
    (f : MvPolynomial σ K) {μ k : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ) (hμ : homogeneousComponent μ f ≠ 0)
    (hk : μ ≤ k) :
    Module.finrank K (originLayer f k) +
      Module.finrank K (homogeneousSubmodule σ K (k - μ)) =
      Module.finrank K (homogeneousSubmodule σ K k) := by
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  let V := homogeneousSubmodule σ K k
  have hker : V ⊓ φ.ker = homogeneousMultiples (homogeneousComponent μ f) μ k := by
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      obtain ⟨u, hu, he⟩ := (homogeneous_mem_originTruncation_iff hf hμ hk hx).mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      exact Submodule.mem_map.mpr ⟨u, hu, he⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      refine ⟨?_, Ideal.Quotient.eq_zero_iff_mem.mpr
        (initial_form_multiple_mem_truncation hf hk hu)⟩
      change (homogeneousComponent μ f * u).IsHomogeneous k
      simpa only [Nat.add_sub_of_le hk] using (homogeneousComponent_isHomogeneous μ f).mul hu
  let _ : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg σ K k)
  have h := φ.finrank_map_add_finrank_inf_ker V
  rw [hker, homogeneousMultiples_finrank _ hμ] at h
  rwa [originLayer_eq_homogeneousCoordinateSpace]

/-- Below the equation's first nonzero degree the layer has no relations. -/
private theorem originLayer_hilbert_eq_of_lt [Finite σ]
    (f : MvPolynomial σ K) {μ k : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ) (hk : k < μ) :
    Module.finrank K (originLayer f k) =
      Module.finrank K (homogeneousSubmodule σ K k) := by
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  let V := homogeneousSubmodule σ K k
  have hI : originTruncationIdeal f k ≤ idealOfVars σ K ^ (k + 1) := by
    apply sup_le _ le_rfl
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.pow_le_pow_right (by omega) hf
  have hinj : Function.Injective (φ.domRestrict V) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hzero := homogeneousComponent_eq_zero_of_mem_origin_power
      (hI (Ideal.Quotient.eq_zero_iff_mem.mp hx)) (Nat.lt_succ_self k)
    change homogeneousComponent k (x : MvPolynomial σ K) = 0 at hzero
    rw [homogeneousComponent_eq_self x.property] at hzero
    exact Subtype.ext hzero
  rw [originLayer_eq_homogeneousCoordinateSpace]
  have he := (LinearEquiv.ofInjective (φ.domRestrict V) hinj).finrank_eq.symm
  rw [LinearMap.range_domRestrict] at he
  exact he

/-- CCDN 2.1's exact binomial formula for the origin-adic layers. -/
theorem originLayer_finrank_eq_hypersurfaceLayerBound {n μ k : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f ∈ idealOfVars (Fin (n + 1)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    Module.finrank K (originLayer f k) = hypersurfaceLayerBound n μ k := by
  by_cases hk : μ ≤ k
  · have hh := originLayer_hilbert_eq f hf hμ hk
    rw [finrank_homogeneousSubmodule_fin, finrank_homogeneousSubmodule_fin] at hh
    unfold hypersurfaceLayerBound
    rw [ite_eq_left hk, Nat.choose_symm_add, Nat.choose_symm_add]
    omega
  · rw [originLayer_hilbert_eq_of_lt f hf (by omega), finrank_homogeneousSubmodule_fin]
    simp only [hypersurfaceLayerBound, ite_eq_right hk, Nat.sub_zero]
    exact Nat.choose_symm_add.symm

end
end CCDN
