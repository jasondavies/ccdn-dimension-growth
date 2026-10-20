module

public import CCDN.InfinityParameterReduction
public import Mathlib.RingTheory.Ideal.Operations

/-! Hyperplanes with no common nonzero cone point yield balanced
coordinate-power reductions over their original coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem homogeneous_parameter_power_reduction
    {K σ τ : Type*} [Field K] [Fintype τ]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ M, homogeneousComponent M f ∈ I)
    (a : τ → MvPolynomial σ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (j : σ) (N : ℕ) (hN : 0 < N)
    (hpow : X j ^ N ∈ I ⊔ Ideal.span (Set.range a)) :
    ∃ s : τ → MvPolynomial σ K, (∀ i, (s i).totalDegree ≤ N - 1) ∧
      (Ideal.Quotient.mk I) (X j ^ N) =
        ∑ i, (Ideal.Quotient.mk I) (a i) * (Ideal.Quotient.mk I) (s i) := by
  classical
  cases N with
  | zero => omega
  | succ k =>
    obtain ⟨g,hg,t,ht,he⟩ := Submodule.mem_sup.mp hpow
    obtain ⟨s,hs⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht
    have hm : X j ^ (k + 1) - ∑ i, a i * s i ∈ I := by
      have hh : ∑ i, a i * s i = t := by simpa only [mul_comm] using hs
      rw [hh,← he,add_sub_cancel_right]
      exact hg
    have hcomp := hI _ hm (k + 1)
    rw [map_sub,homogeneousComponent_eq_self (isHomogeneous_X_pow j (k + 1)),map_sum] at hcomp
    have heq (i : τ) : homogeneousComponent (k + 1) (a i * s i) =
        a i * homogeneousComponent k (s i) := by
      rw [show k + 1 = 1 + k by omega]
      exact homogeneousComponent_mul_homogeneous_left (ha i) (s i) k
    simp only [heq] at hcomp
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    rw [map_sub,sub_eq_zero,map_sum] at hq
    refine ⟨fun i => homogeneousComponent k (s i),?_,?_⟩
    · intro i
      simpa only [Nat.add_sub_cancel] using
        (homogeneousComponent_isHomogeneous k (s i)).totalDegree_le
    · simpa only [map_mul] using hq

theorem exists_homogeneous_parameter_power_reductions
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ M, homogeneousComponent M f ∈ I)
    (a : τ → MvPolynomial σ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (I ⊔ Ideal.span (Set.range a)), z = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : σ, ∃ s : τ → MvPolynomial σ K,
      (∀ i, (s i).totalDegree ≤ N - 1) ∧
      (Ideal.Quotient.mk I) (X j ^ N) =
        ∑ i, (Ideal.Quotient.mk I) (a i) * (Ideal.Quotient.mk I) (s i) := by
  classical
  let J := I ⊔ Ideal.span (Set.range a)
  have hp (j : σ) : ∃ M : ℕ, X j ^ M ∈ J := by
    have hm : X j ∈ vanishingIdeal K (MvPolynomial.zeroLocus L J) := by
      intro z hz
      rw [hzero z hz]
      simp
    rw [vanishingIdeal_zeroLocus_eq_radical] at hm
    exact hm
  choose M hM using hp
  let N := Finset.univ.sup M + 1
  have hN : 0 < N := by dsimp [N]; omega
  refine ⟨N,hN,?_⟩
  intro j
  apply homogeneous_parameter_power_reduction I hI a ha j N hN
  have hj : M j ≤ N := (Finset.le_sup (f := M) (Finset.mem_univ j)).trans (Nat.le_succ _)
  have hh := J.mul_mem_left (X j ^ (N - M j)) (hM j)
  simpa only [← pow_add,Nat.sub_add_cancel hj] using hh

end
end CCDN
