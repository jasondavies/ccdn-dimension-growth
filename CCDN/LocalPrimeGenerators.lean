module

public import CCDN.LocalPrimeReduction

/-! Lift bases of mod-prime local layers to a Noetherian local ring.
The resulting generators belong to the correct maximal-ideal powers, and
their approximation errors are explicit sums of a high-order term and a
multiple of the prime. Iterating the latter gives any finite precision. -/

@[expose] public section
namespace CCDN
noncomputable section
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]

/-- Lift the quotient-layer generators to the corresponding ideal
powers in the original local ring. -/
theorem exists_local_prime_generators [IsNoetherianRing R] (ρ : R →+* ZMod p) :
    ∃ G : (k : ℕ) → Fin (localPrimeLayerDimension R p k) → R,
      (∀ k j, G k j ∈ maximalIdeal R ^ k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (localPrimeLayerDimension R p k.val) → ℤ)
        (v w : R), v ∈ maximalIdeal R ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • G k.val j = v + (p : R) * w := by
  classical
  let q := Ideal.Quotient.mk (Ideal.span {(p : R)})
  obtain ⟨g, hg, hspan⟩ := exists_localPrimeReduction_generators ρ
  have hlift (k : ℕ) (j : Fin (localPrimeLayerDimension R p k)) :
      ∃ G : R, G ∈ maximalIdeal R ^ k ∧ q G = g k j := by
    apply (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    rw [Ideal.map_pow]
    exact hg k j
  choose G hG hqG using hlift
  refine ⟨G, hG, ?_⟩
  intro N u
  obtain ⟨c, hc⟩ := hspan N (q u)
  let cZ : (k : Fin N) → Fin (localPrimeLayerDimension R p k.val) → ℤ :=
    fun k j => (c k j).val
  have hcoeff (a : ZMod p) :
      ((a.val : ℤ) : LocalPrimeReduction R p) =
        algebraMap (ZMod p) (LocalPrimeReduction R p) a := by
    rw [Int.cast_natCast, ← map_natCast (algebraMap (ZMod p) (LocalPrimeReduction R p)),
      ZMod.natCast_zmod_val]
  let S : R := ∑ k : Fin N, ∑ j, cZ k j • G k.val j
  have hS : q S = ∑ k : Fin N, ∑ j, c k j • g k.val j := by
    simp only [S, cZ, map_sum, Algebra.smul_def, algebraMap_int_eq,
      Int.coe_castRingHom, map_mul, map_intCast, hqG, hcoeff]
  have hvex : ∃ v : R, v ∈ maximalIdeal R ^ N ∧ q v = q u - q S := by
    apply (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    rw [Ideal.map_pow, hS]
    exact hc
  obtain ⟨v, hv, hqv⟩ := hvex
  have hD : q (u - S - v) = 0 := by
    rw [map_sub, map_sub, hqv]
    ring
  have hmem : u - S - v ∈ Ideal.span {(p : R)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hD
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨cZ, v, w, hv, ?_⟩
  change u - S = v + (p : R) * w
  linear_combination hw

omit [IsLocalRing R] [Fact p.Prime] in
/-- Iterate a prime-divisible remainder inside the ring itself. This is
independent of the subsequent family of evaluation homomorphisms. -/
lemma local_prime_generators_approximate (I : Ideal R) (r : ℕ → ℕ)
    (G : (k : ℕ) → Fin (r k) → R) (N : ℕ)
    (hrep : ∀ u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (v w : R),
      v ∈ I ^ N ∧ u - ∑ k : Fin N, ∑ j, c k j • G k.val j = v + (p : R) * w) :
    ∀ e u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (v w : R),
      v ∈ I ^ N ∧ u - ∑ k : Fin N, ∑ j, c k j • G k.val j = v + (p : R) ^ e * w := by
  classical
  intro e
  induction e with
  | zero =>
    intro u
    exact ⟨fun _ _ => 0, 0, u, (I ^ N).zero_mem, by simp⟩
  | succ e ih =>
    intro u
    obtain ⟨c, v, w, hv, he⟩ := hrep u
    obtain ⟨b, v', w', hv', he'⟩ := ih w
    refine ⟨fun k j => c k j + (p : ℤ) * b k j, v + (p : R) * v', w',
      (I ^ N).add_mem hv ((I ^ N).mul_mem_left _ hv'), ?_⟩
    simp only [add_smul, mul_smul, Finset.sum_add_distrib,
      zsmul_eq_mul, Int.cast_natCast, ← Finset.mul_sum]
    simp only [zsmul_eq_mul] at he he'
    rw [pow_succ]
    linear_combination he + (p : R) * he'

/-- The weighted generators approximate every ring element modulo
`m^N + (p^e)`. -/
theorem exists_local_prime_approximations [IsNoetherianRing R] (ρ : R →+* ZMod p) :
    ∃ G : (k : ℕ) → Fin (localPrimeLayerDimension R p k) → R,
      (∀ k j, G k j ∈ maximalIdeal R ^ k) ∧
      ∀ N e u, ∃ (c : (k : Fin N) → Fin (localPrimeLayerDimension R p k.val) → ℤ)
        (v w : R), v ∈ maximalIdeal R ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • G k.val j = v + (p : R) ^ e * w := by
  obtain ⟨G, hG, hrep⟩ := exists_local_prime_generators ρ
  exact ⟨G, hG, fun N => local_prime_generators_approximate
    (maximalIdeal R) _ G N (hrep N)⟩

end
end CCDN
