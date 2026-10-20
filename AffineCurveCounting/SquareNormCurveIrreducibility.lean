module

public import AffineCurveCounting.NormPolynomialSubfield
public import AffineCurveCounting.OddDegreeNormCurves

/-! A double-cover polynomial with an odd root multiplicity is
irreducible. Applied to the norm-polynomial factorization, this detects
the genuine even-index subfield exceptions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial NumberField IntermediateField Module
open scoped IntermediateField Classical

lemma rootMultiplicity_pow_exact {F : Type*} [Field F] (p : F[X]) (hp : p ≠ 0)
    (a : F) (n : ℕ) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]
    ring

lemma odd_rootMultiplicity_not_square_ratFunc {F : Type*} [Field F]
    (p : F[X]) (hp : p ≠ 0) (a : F) (ha : Odd (rootMultiplicity a p))
    (b : RatFunc F) :
    b ^ 2 ≠ algebraMap F[X] (RatFunc F) p := by
  intro he
  have hi := IsFractionRing.injective F[X] (RatFunc F)
  have hd : algebraMap F[X] (RatFunc F) b.denom ≠ 0 := by
    intro h
    exact b.denom_ne_zero (hi (by simpa using h))
  have hb : b ≠ 0 := by
    intro h
    have hh : algebraMap F[X] (RatFunc F) p = 0 := by simpa [h] using he.symm
    exact hp (hi (by simpa using hh))
  have hnum : b.num ≠ 0 := RatFunc.num_ne_zero hb
  have hrepr : algebraMap F[X] (RatFunc F) b.num =
      b * algebraMap F[X] (RatFunc F) b.denom :=
    (div_eq_iff hd).mp b.num_div_denom
  have hpoly : b.num ^ 2 = p * b.denom ^ 2 := by
    apply hi
    rw [map_pow, map_mul, map_pow, hrepr, mul_pow, he]
  have hm := congrArg (rootMultiplicity a) hpoly
  rw [rootMultiplicity_pow_exact _ hnum,
    rootMultiplicity_mul (mul_ne_zero hp (pow_ne_zero _ b.denom_ne_zero)),
    rootMultiplicity_pow_exact _ b.denom_ne_zero] at hm
  obtain ⟨k, hk⟩ := ha
  omega

lemma double_cover_irreducible_of_odd_root_multiplicity {F : Type*} [Field F]
    (p : F[X]) (hp : p ≠ 0) (a : F) (ha : Odd (rootMultiplicity a p)) :
    Irreducible (X ^ 2 - C p : F[X][X]) := by
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc F) (monic_X_pow_sub_C p (by decide : (2 : ℕ) ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (odd_rootMultiplicity_not_square_ratFunc p hp a ha)

lemma separable_odd_power_double_cover_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    (p : F[X]) (hp : p.Separable) (hd : 0 < p.natDegree)
    {c : F} (hc : c ≠ 0) {e : ℕ} (he : Odd e) :
    Irreducible (X ^ 2 - C (C c * p ^ e) : F[X][X]) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hd))
  have hm : rootMultiplicity a p = 1 := by
    have hpos := (rootMultiplicity_pos hp0).mpr ha
    have hle := rootMultiplicity_le_one_of_separable hp a
    omega
  apply double_cover_irreducible_of_odd_root_multiplicity (C c * p ^ e)
    (mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hp0)) a
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hp0)),
    rootMultiplicity_C, rootMultiplicity_pow_exact _ hp0, hm, mul_one, zero_add]
  exact he

/-- Odd multiplicity of the generated subfield suffices, even when the
ambient number-field degree itself is even. -/
theorem signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K)) :
    Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
      (signedNormCurvePolynomial K β ε)) := by
  apply (MulEquiv.irreducible_iff
    (f := bivariatePolynomialEquiv (AlgebraicClosure ℚ))).mp
  rw [← bivariatePolynomialEquiv_map]
  simp only [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
  change Irreducible (Polynomial.map
    (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))
    (X ^ 2 - C (C ε * integerNormPolynomial K β)))
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_mul]
  rw [integerNormPolynomial_map_eq_minpoly_pow_algebraicClosure]
  have hβ : IsIntegral ℚ (β : K) := IsIntegral.of_finite ℚ (β : K)
  apply separable_odd_power_double_cover_irreducible
    ((minpoly ℚ (β : K)).map (algebraMap ℚ (AlgebraicClosure ℚ)))
    ((minpoly.irreducible hβ).separable.map) _ _ hindex
  · rw [(minpoly.monic hβ).natDegree_map]
    exact minpoly.natDegree_pos hβ
  · change (ε : AlgebraicClosure ℚ) ≠ 0
    exact_mod_cast hε

/-- Every reducible signed norm curve comes from a parameter whose
generated subfield has even index. -/
theorem signedNormCurvePolynomial_reducible_implies_even_subfield_index
    (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hir : ¬ Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
      (signedNormCurvePolynomial K β ε))) :
    Even (Module.finrank ℚ⟮(β : K)⟯ K) := by
  rcases Nat.even_or_odd (Module.finrank ℚ⟮(β : K)⟯ K) with he | ho
  · exact he
  · exact (hir (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
      K β hε ho)).elim

theorem signedNormCurvePolynomial_reducible_small_subfield
    (K : Type*) [Field K] [NumberField K]
    (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2)
    (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hir : ¬ Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
      (signedNormCurvePolynomial K β ε))) :
    ∃ L : IntermediateField ℚ K, (β : K) ∈ L ∧
      4 ≤ Module.finrank L K ∧
      4 * Module.finrank ℚ L ≤ Module.finrank ℚ K := by
  let L := ℚ⟮(β : K)⟯
  have he := signedNormCurvePolynomial_reducible_implies_even_subfield_index K β hε hir
  have hpos : 0 < Module.finrank L K := Module.finrank_pos
  have hne := hnoTwo L
  have hfour : 4 ≤ Module.finrank L K := by
    obtain ⟨k, hk⟩ := he
    change Module.finrank L K = k + k at hk
    omega
  refine ⟨L, IntermediateField.mem_adjoin_simple_self ℚ (β : K), hfour, ?_⟩
  have hdim := Module.finrank_mul_finrank ℚ L K
  nlinarith

end
end AffineCurveCounting
