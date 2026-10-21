/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfaceBadPrimes
public import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Auxiliary.UniversalPlaneBadReduction
/-! A nonzero bad-prime witness obtained by evaluating the universal
plane polynomial on a bounded integer grid. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma bad_prime_dvd_universalPlaneBadWitness_eval {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (p : ℕ)
    (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
    (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  classical
  obtain ⟨hpprime, hbad⟩ := hbad
  let : Fact p.Prime := ⟨hpprime⟩
  rw [eval_eq']
  apply Finset.dvd_sum
  intro e _
  exact dvd_mul_of_dvd_left
    (bad_prime_dvd_universalPlaneBadWitness_coeff f hpos rows cols p hp hbad e) _

/-- The universal plane bad-prime witness of an absolutely irreducible integer polynomial
takes a nonzero value at some integer parameter in the box `[0, 2d³]`, and every prime above
`d` with bad geometric reduction divides that value. -/
theorem exists_bounded_integer_plane_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
      (v : PlaneParameters (Option σ) → ℤ),
      (∀ i, 0 ≤ v i ∧ v i ≤ (2 * f.totalDegree ^ 3 : ℕ)) ∧
      eval v (universalPlaneBadWitness f rows cols) ≠ 0 ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p →
        (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  obtain ⟨rows, cols, hw, hd⟩ := exists_integer_universalPlane_badWitness f hf hpos
  obtain ⟨v, hv, he⟩ := exists_integer_grid_eval_ne_zero _ hw _ hd
  exact ⟨rows, cols, v, hv, he,
    fun p hp hbad => bad_prime_dvd_universalPlaneBadWitness_eval f hpos rows cols v p hp hbad⟩

end
end CCDN
