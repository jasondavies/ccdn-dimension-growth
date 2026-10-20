module

public import CCDN.BoundedDegreeNormalizationFiber
public import CCDN.BoundedLinearSeparation
public import CCDN.LinearNormalizationInfinite

/-! Fibers of a linear normalization are finite. An additional
homogeneous linear form separates an outside point from the whole fiber. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem linear_normalization_fiber_finite
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (z : Fin (m + 1) → K) :
    {x : Fin n → K | (∀ f ∈ I, eval x f = 0) ∧ ∀ i, eval x (l i) = z i}.Finite := by
  classical
  by_contra h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (d + 1)
  have hh := bounded_degree_normalization_fiber_card_le I 1 (by omega) l hl hi hint
    d hdim hdegree z s (fun x hx => (hs hx).1) (fun x hx => (hs hx).2)
  simp only [one_pow, mul_one, hcard] at hh
  omega

theorem exists_linear_form_separating_finite_set
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (s : Finset (Fin n → K)) (z : Fin n → K) (hz : z ∉ s) :
    ∃ t : MvPolynomial (Fin n) K, t.IsHomogeneous 1 ∧
      ∀ x ∈ s, eval x t ≠ eval z t := by
  classical
  let S := insert z s
  obtain ⟨k, _, hk⟩ := exists_bounded_moment_separation
    (fun x : S => x.val) Subtype.val_injective
  let t : MvPolynomial (Fin n) K := ∑ j : Fin n, C ((k : K) ^ j.val) * X j
  have ht (x : Fin n → K) : eval x t = ∑ j : Fin n, x j * (k : K) ^ j.val := by
    simp only [t, map_sum, eval_mul, eval_C, eval_X, mul_comm]
  refine ⟨t, IsHomogeneous.sum _ _ 1 (fun j _ => isHomogeneous_C_mul_X _ _), ?_⟩
  intro x hx he
  have hxe : (⟨x, Finset.mem_insert_of_mem hx⟩ : S) =
      ⟨z, Finset.mem_insert_self _ _⟩ := by
    apply hk
    simpa only [← ht] using he
  have hxz : x = z := congrArg Subtype.val hxe
  exact hz (hxz ▸ hx)

end
end CCDN
