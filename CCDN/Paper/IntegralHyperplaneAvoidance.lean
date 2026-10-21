/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.HyperplaneSectionIdeal
import CCDN.Hypersurface.EffectiveHyperplaneAvoidance

/-! Effective avoidance for the homogeneous hyperplane intersection
ideal, including degree one and coincident hyperplanes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
universe u

/-- For the hyperplane `A · x = 0` with `A none ≠ 0`, if the restriction of `f` to the hyperplane,
written as a graph over the other coordinates, is absolutely irreducible, then the ideal generated
by `f` and the linear form is prime over the algebraic closure; used for CCDN Lemma 4.3.7. -/
lemma hyperplaneSectionIdeal_isPrime_of_absolute_graph {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    (f : MvPolynomial (Option σ) K)
    (hir : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (graphHyperplaneRestriction (fun i => -A (some i) / A none) f))) :
    (Ideal.span {map (algebraMap K (AlgebraicClosure K)) f,
      linearForm (algebraMap K (AlgebraicClosure K) ∘ A)}).IsPrime := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hA' : (φ ∘ A) none ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hA
  rw [hyperplaneSectionIdeal_graph (φ ∘ A) hA']
  have hg : Irreducible
      (graphHyperplaneRestriction (fun i => -(φ ∘ A) (some i) / (φ ∘ A) none)
        (map φ f)) := by
    have he : (fun i => -(φ ∘ A) (some i) / (φ ∘ A) none) =
        φ ∘ (fun i => -A (some i) / A none) := by
      funext i
      simp only [Function.comp_apply, map_div₀, map_neg]
    rw [he, ← graphHyperplaneRestriction_map]
    exact hir
  let : (Ideal.span
      {graphHyperplaneRestriction (fun i => -(φ ∘ A) (some i) / (φ ∘ A) none)
        (map φ f)}).IsPrime := (Ideal.span_singleton_prime hg.ne_zero).mpr hg.prime
  exact Ideal.comap_isPrime _ _

/-- The corrected degree bound in CCDN 4.3.7 for every positive degree,
using primeness of the intersection ideal after algebraic closure.
For degree one the detector is the constant one. -/
theorem exists_integral_hyperplane_avoidance {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (hir : AbsolutelyIrreducible f) :
    ∃ (G : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ) (e : ℕ),
      G ≠ 0 ∧ G.IsHomogeneous e ∧ e ≤ (4 + n) * d * (d ^ 2 - 1) ∧
      ∀ (K : Type u) [Field K] (A : Option (Option (Fin (2 + n))) → K),
        ¬ (Ideal.span {map (Int.castRingHom (AlgebraicClosure K)) f,
          linearForm (algebraMap K (AlgebraicClosure K) ∘ A)}).IsPrime →
        eval₂ (Int.castRingHom K) A G = 0 := by
  by_cases hd1 : d = 1
  · subst d
    refine ⟨1, 0, one_ne_zero, isHomogeneous_one _ _, by simp, ?_⟩
    intro K _ A hbad
    exact (hbad (homogeneous_linear_hyperplane_section_isPrime _ _
      (hf.map (Int.castRingHom (AlgebraicClosure K))))).elim
  · obtain ⟨G, hG, hGhom, hGdeg, hGbad⟩ :=
      exists_effective_hyperplane_avoidance f d (by omega) hf hir
    refine ⟨G, d * (d ^ 2 - 1) + 1, hG, hGhom, ?_, ?_⟩
    · rwa [← hGhom.totalDegree hG]
    · intro K _ A hbad
      apply hGbad K A
      intro hA hirA
      apply hbad
      have hp := hyperplaneSectionIdeal_isPrime_of_absolute_graph A hA
        (map (Int.castRingHom K) f) hirA
      have he : map (algebraMap K (AlgebraicClosure K))
          (map (Int.castRingHom K) f) = map (Int.castRingHom (AlgebraicClosure K)) f := by
        rw [map_map]
        congr 1
      rwa [he] at hp

end
end CCDN
