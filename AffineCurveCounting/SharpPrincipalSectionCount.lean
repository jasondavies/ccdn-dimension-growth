module

public import AffineCurveCounting.PrincipalSectionGridBound
public import AffineCurveCounting.NonabsoluteHypersurfaceCount

/-! Sharp integer-box bounds for proper polynomial sections. In particular,
the exact constant-one bound of CCDN Corollary 4.1.4 holds for every
non-absolutely-irreducible rational hypersurface. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem principal_section_count_le_box
    {n m : ℕ} (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (f : CoordinatePolynomial n) (hf : f ∉ I) {B : ℝ} (hB : 0 ≤ B) :
    (count (idealZeroLocus I ∩ zeroLocus f) B : ℝ) ≤
      d * (f.totalDegree : ℝ) * (2 * B + 1) ^ m := by
  classical
  let T := integralPoints (idealZeroLocus I ∩ zeroLocus f) B
  let S : Finset ℚ := (Finset.Icc (-⌊B⌋) ⌊B⌋).image (fun t : ℤ => (t : ℚ))
  have hi : Function.Injective (rationalPoint : IntPoint n → RatPoint n) := by
    intro x y h
    funext i
    exact Int.cast_injective (congrFun h i)
  have hz : ∀ x ∈ T.image rationalPoint, ∀ g ∈ I, eval x g = 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_integralPoints.mp ha).2.1
  have hzf : ∀ x ∈ T.image rationalPoint, eval x f = 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_integralPoints.mp ha).2.2
  have hg : ∀ x ∈ T.image rationalPoint, ∀ i, x i ∈ S := by
    intro x hx i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨a i, ?_, rfl⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp ha).1 i)
    have hn : -(a i) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩
  have hh := principal_section_grid_card_le I d hdim hdegree f hf S
    (T.image rationalPoint) hz hzf hg
  rw [Finset.card_image_of_injective _ hi] at hh
  have hcard : (count (idealZeroLocus I ∩ zeroLocus f) B : ℝ) ≤
      d * (f.totalDegree : ℝ) * (S.card : ℝ) ^ m := by exact_mod_cast hh
  have hScard : (S.card : ℝ) ≤ 2 * B + 1 := by
    have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith [Int.floor_le B]
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hScard m) (by positivity))

theorem proper_hypersurface_intersection_count_le_sharp
    {n : ℕ} (f g : CoordinatePolynomial (n + 2)) (hf : Prime f) (hfg : ¬ f ∣ g)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f ∩ zeroLocus g) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) ^ n := by
  let I : Ideal (CoordinatePolynomial (n + 2)) := Ideal.span {f}
  let : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hfdeg : 0 < f.totalDegree := by
    by_contra! h
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hc : f.coeff 0 ≠ 0 := by
      intro hc
      exact hf.ne_zero (by rw [he, hc, map_zero])
    exact hf.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)
  have hzero : idealZeroLocus I = zeroLocus f := by
    ext x
    constructor
    · intro hx
      exact hx f (Ideal.subset_span (Set.mem_singleton f))
    · intro hx
      change Ideal.span {f} ≤ RingHom.ker (eval x)
      apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact hx
  have hh := principal_section_count_le_box I f.totalDegree
    (principal_filteredHilbertPolynomial_natDegree f hf.ne_zero hfdeg)
    (principal_filteredHilbertPolynomial_leadingCoeff f hf.ne_zero hfdeg)
    g (fun h => hfg (Ideal.mem_span_singleton.mp h)) hB
  simpa only [hzero] using hh

/-- Exact quadratic-degree nonabsolute hypersurface bound, with no
auxiliary equation supplied and no extra dimension-dependent factor. -/
theorem nonabsolute_hypersurface_count_le_sharp
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (f : CoordinatePolynomial (n + 2)) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤
      (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨g, _, hgd, hfg, hzero⟩ := nonabsolute_affine_auxiliary f hir hred
  have hsubset : zeroLocus f ⊆ zeroLocus f ∩ zeroLocus g := fun x hx => ⟨hx, hzero x hx⟩
  have hcount : (count (zeroLocus f) B : ℝ) ≤
      count (zeroLocus f ∩ zeroLocus g) B := by
    exact_mod_cast count_mono hsubset le_rfl
  have hh := hcount.trans (proper_hypersurface_intersection_count_le_sharp f g hir.prime hfg hB)
  apply hh.trans
  rw [pow_two]
  gcongr

end
end AffineCurveCounting
