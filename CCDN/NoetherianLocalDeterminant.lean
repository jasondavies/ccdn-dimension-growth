module

public import CCDN.LocalPrimeGenerators
public import CCDN.ExactFiltrationWeights

/-! Determinants of homomorphisms from arbitrary Noetherian local
rings. The residue map of the target identifies its prime ideal; all local
generators and their finite-precision factorizations are constructed from
the source ring and its mod-prime ideal layers. -/

@[expose] public section
namespace CCDN
noncomputable section
open IsLocalRing

lemma ring_dvd_det_sub_of_dvd_entries {S : Type*} [CommRing S] {s : ℕ}
    (A B : Matrix (Fin s) (Fin s) S) (m : S)
    (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  let I : Ideal S := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    ext i j
    apply sub_eq_zero.mp
    change φ (A i j) - φ (B i j) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))
  apply Ideal.mem_span_singleton.mp
  change A.det - B.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (A.det - B.det) = 0
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
  {p : ℕ} [Fact p.Prime]

/-- Every homomorphism to a ring with residue quotient `F_p` sends the
maximal ideal of the local source into the target's prime ideal. -/
lemma local_map_maximalIdeal_dvd (τ : S →+* ZMod p)
    (hτ : RingHom.ker τ = Ideal.span {(p : S)}) (ψ : R →+* S)
    {x : R} (hx : x ∈ maximalIdeal R) : (p : S) ∣ ψ x := by
  have hk := local_zmod_kernel (τ.comp ψ)
  rw [← hk] at hx
  have hm : ψ x ∈ RingHom.ker τ := hx
  rw [hτ] at hm
  exact Ideal.mem_span_singleton.mp hm

lemma local_map_maximalIdeal_pow_dvd (τ : S →+* ZMod p)
    (hτ : RingHom.ker τ = Ideal.span {(p : S)}) (ψ : R →+* S)
    {N : ℕ} {x : R} (hx : x ∈ maximalIdeal R ^ N) :
    (p : S) ^ N ∣ ψ x := by
  have hI : maximalIdeal R ≤ (Ideal.span {(p : S)}).comap ψ := by
    intro a ha
    exact Ideal.mem_span_singleton.mpr (local_map_maximalIdeal_dvd τ hτ ψ ha)
  have hpow := (pow_le_pow_left' hI N).trans (Ideal.le_comap_pow ψ N)
  have hmem := hpow hx
  change ψ x ∈ (Ideal.span {(p : S)}) ^ N at hmem
  rw [Ideal.span_singleton_pow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-- The weighted determinant principle for Noetherian local rings.
The only numerical input specifies the exponent in terms of the
layer dimensions. -/
theorem noetherian_local_det_of_weight_threshold [IsNoetherianRing R] {s e : ℕ}
    (τ : S →+* ZMod p) (hτ : RingHom.ker τ = Ideal.span {(p : S)})
    (ψ : Fin s → R →+* S) (x : Fin s → R)
    (he : ∀ t : Fin s ↪ ((k : Fin e) × Fin (localPrimeLayerDimension R p k.val)),
      e ≤ ∑ i, (t i).1.val) :
    (p : S) ^ e ∣ (Matrix.of fun i j => ψ i (x j)).det := by
  classical
  by_cases hs : 0 < s
  · obtain ⟨G, hG, hrep⟩ := exists_local_prime_approximations (τ.comp (ψ ⟨0, hs⟩))
    choose c v w hv hcw using fun j => hrep e e (x j)
    have hdiv (i : Fin s) (z : (k : Fin e) × Fin (localPrimeLayerDimension R p k.val)) :
        (p : S) ^ z.1.val ∣ ψ i (G z.1.val z.2) :=
      local_map_maximalIdeal_pow_dvd τ hτ (ψ i) (hG z.1.val z.2)
    choose U₀ hU using hdiv
    let U : Matrix (Fin s) ((k : Fin e) × Fin (localPrimeLayerDimension R p k.val)) S := U₀
    let V : Matrix ((k : Fin e) × Fin (localPrimeLayerDimension R p k.val)) (Fin s) S :=
      fun z j => (p : S) ^ z.1.val * (c j z.1 z.2 : S)
    have hdet : (p : S) ^ e ∣ (U * V).det :=
      pow_dvd_det_of_weighted_factorization_fintype U V (p : S) (fun z => z.1.val) e
        (fun _ _ => dvd_mul_right _ _) he
    have hprod (i j : Fin s) : (U * V) i j =
        ∑ k : Fin e, ∑ l, (c j k l : S) * ψ i (G k.val l) := by
      rw [Matrix.mul_apply, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [hU i ⟨k, l⟩]
      dsimp only [U, V]
      ring
    have hcong (i j : Fin s) : (p : S) ^ e ∣ ψ i (x j) - (U * V) i j := by
      rw [hprod]
      have h := congrArg (ψ i) (hcw j)
      simp only [map_sub, map_sum, map_add, map_mul, map_pow, map_natCast,
        zsmul_eq_mul, map_intCast] at h
      rw [h]
      exact dvd_add (local_map_maximalIdeal_pow_dvd τ hτ (ψ i) (hv j))
        (dvd_mul_right _ _)
    have hd := ring_dvd_det_sub_of_dvd_entries (Matrix.of fun i j => ψ i (x j))
      (U * V) ((p : S) ^ e) hcong
    simpa only [sub_add_cancel] using dvd_add hd hdet
  · have hs0 : s = 0 := by omega
    subst s
    have ht : Fin 0 ↪ ((k : Fin e) × Fin (localPrimeLayerDimension R p k.val)) :=
      ⟨Fin.elim0, by intro a; exact Fin.elim0 a⟩
    have he0 := he ht
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.le_zero] at he0
    subst e
    simp

/-- General local-ring counterpart of the hypersurface filtration
divisor. The layer profile is that of the quotient `R/(p)`. -/
theorem noetherian_local_filtration_det [IsNoetherianRing R] {s : ℕ}
    (τ : S →+* ZMod p) (hτ : RingHom.ker τ = Ideal.span {(p : S)})
    (ψ : Fin s → R →+* S) (x : Fin s → R) :
    (p : S) ^ filtrationExponent (localPrimeLayerDimension R p) s ∣
      (Matrix.of fun i j => ψ i (x j)).det :=
  noetherian_local_det_of_weight_threshold τ hτ ψ x
    (fun t => filtrationExponent_le_weights (localPrimeLayerDimension R p) t)

/-- The exact sum of the first `s` local-layer weights is a determinant
divisor, in every dimension and without asymptotic approximation. -/
theorem noetherian_local_initial_weight_det [IsNoetherianRing R] {s : ℕ}
    (τ : S →+* ZMod p) (hτ : RingHom.ker τ = Ideal.span {(p : S)})
    (ψ : Fin s → R →+* S) (x : Fin s → R) (w : Fin s → ℕ)
    (hw : IsInitialWeightSegment (localPrimeLayerDimension R p) w) :
    (p : S) ^ (∑ i, w i) ∣ (Matrix.of fun i j => ψ i (x j)).det :=
  noetherian_local_det_of_weight_threshold τ hτ ψ x
    (fun t => initial_weight_sum_le_embedding (localPrimeLayerDimension R p) w hw t)

end
end CCDN
