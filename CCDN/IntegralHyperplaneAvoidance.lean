module

public import CCDN.HyperplaneSectionIdeal
public import CCDN.EffectiveHyperplaneAvoidance

/-! Effective avoidance for the actual homogeneous hyperplane intersection
ideal, including degree one and coincident hyperplanes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
universe u

lemma hyperplaneSectionIdeal_isPrime_of_absolute_graph {K σ : Type*}
    [Field K] [Fintype σ] (A : Option σ → K) (hA : A none ≠ 0)
    (f : MvPolynomial (Option σ) K)
    (hir : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (graphHyperplaneRestriction (fun i => -A (some i) / A none) f))) :
    (Ideal.span {map (algebraMap K (AlgebraicClosure K)) f,
      hyperplaneNormalPolynomial (algebraMap K (AlgebraicClosure K) ∘ A)}).IsPrime := by
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
using primeness of the actual intersection ideal after algebraic closure.
For degree one the detector is the constant one. -/
theorem exists_integral_hyperplane_avoidance {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f)) :
    ∃ (G : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ) (e : ℕ),
      G ≠ 0 ∧ G.IsHomogeneous e ∧ e ≤ (4 + n) * d * (d ^ 2 - 1) ∧
      ∀ (K : Type u) [Field K] (A : Option (Option (Fin (2 + n))) → K),
        ¬ (Ideal.span {map (Int.castRingHom (AlgebraicClosure K)) f,
          hyperplaneNormalPolynomial (algebraMap K (AlgebraicClosure K) ∘ A)}).IsPrime →
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
