/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularTangent
import CCDN.Determinant.OriginLayerGenerators
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.LinearCombination
/-! Finite-precision generation of hypersurface local quotients.
Generator counts equal the layer dimensions; for plane curves each
weight needs at most μ generators. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Successive layer reductions assemble into a finite-precision
polynomial representation, modulo the defining equation and the Nth origin power. -/
lemma origin_layers_generate_truncation {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → MvPolynomial σ K)
    (hspan : ∀ k u, u ∈ idealOfVars σ K ^ k → ∃ c : Fin (r k) → K,
      u - ∑ j, c j • g k j ∈ originTruncationIdeal f k)
    (N : ℕ) (u : MvPolynomial σ K) :
    ∃ c : (k : Fin N) → Fin (r k.val) → K,
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ N := by
  induction N with
  | zero =>
    refine ⟨fun k => Fin.elim0 k, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hc
    obtain ⟨b, hb⟩ := hspan N q hq
    let c' : (k : Fin (N + 1)) → Fin (r k.val) → K := Fin.lastCases b c
    refine ⟨c', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    have hp' : p ∈ Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1) := Submodule.mem_sup_left hp
    have hadd := (Ideal.span {f} ⊔ idealOfVars σ K ^ (N + 1)).add_mem hp' hb
    convert hadd using 1
    linear_combination -he

/-- In every ambient dimension, the numbers of homogeneous generators are
exactly the dimensions of the origin-adic layers. -/
theorem exists_origin_truncation_generators {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin (n + 1)) K),
      (∀ k, r k = Module.finrank K (originLayer f k)) ∧
      (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin (n + 1)) K ^ N := by
  classical
  choose r g hr hg hs using fun k => exists_originLayer_generators f k
  exact ⟨r, g, hr, hg, origin_layers_generate_truncation f r g hs⟩

/-- Finite-precision weighted generators for any plane equation of
multiplicity μ. -/
theorem exists_plane_truncation_generators {K : Type*} [Field K] {μ : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f ∈ idealOfVars (Fin 2) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) K),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ c : (k : Fin N) → Fin (r k.val) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈
          Ideal.span {f} ⊔ idealOfVars (Fin 2) K ^ N := by
  obtain ⟨r, g, hr, hg, hs⟩ := exists_plane_origin_generators f hf hμ
  exact ⟨r, g, hr, hg, origin_layers_generate_truncation f r g hs⟩

end
end CCDN
