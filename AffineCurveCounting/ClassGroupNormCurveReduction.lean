module

public import AffineCurveCounting.ClassGroupTranslateFibers
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The actual bounded square-norm set is partitioned by integer translations.
This constructs the finite norm-curve family rather than assuming one. The
uniform estimate for the number of translation classes is a separate lattice
theorem and is not asserted here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

abbrev IntegerTranslationQuotient :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples (1 : 𝓞 K)

def boundedSquareNormTranslationClasses (B : ℝ) :
    Finset (IntegerTranslationQuotient K) := by
  classical
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    (fun α : 𝓞 K ↦ (α : IntegerTranslationQuotient K))

theorem exists_actual_norm_curve_family (B : ℝ) :
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      Function.Injective β ∧
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      (boundedSquareNormIntegers K B).ncard ≤
        ∑ q : boundedSquareNormTranslationClasses K B,
          (count (signedNormCurveLocus K (β q) 1)
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
          count (signedNormCurveLocus K (β q) (-1))
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K)))) := by
  classical
  let S := boundedSquareNormIntegers K B
  let sf := (boundedSquareNormIntegers_finite K B).toFinset
  let Q := boundedSquareNormTranslationClasses K B
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ S ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  let β : Q → 𝓞 K := fun q ↦ -r q
  have hinj : Function.Injective β := by
    intro q t h
    have he : r q = r t := neg_injective h
    apply Subtype.ext
    rw [← hq q, ← hq t, he]
  have hb (q : Q) (w : InfinitePlace K) : w (β q : K) ≤ B := by
    change w.val (-((r q : 𝓞 K) : K)) ≤ B
    rw [AbsoluteValue.map_neg]
    exact (hr q).2.1 w
  refine ⟨β, hinj, hb, ?_⟩
  let tf (q : Q) := (squareNormTranslateFiber_finite K (β q) B).toFinset
  have hcover : sf ⊆ Finset.univ.biUnion tf := by
    intro α hα
    have hαS : α ∈ S := (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα
    let q : Q := ⟨(α : IntegerTranslationQuotient K),
      Finset.mem_image.mpr ⟨α, hα, rfl⟩⟩
    have he : (α : IntegerTranslationQuotient K) = (r q : IntegerTranslationQuotient K) :=
      (hq q).symm
    obtain ⟨x, hx⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (QuotientAddGroup.eq_iff_sub_mem.mp he)
    have hx' : (x : 𝓞 K) = α - r q := by simpa using hx
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ q,
      (squareNormTranslateFiber_finite K (β q) B).mem_toFinset.mpr ⟨hαS, x, ?_⟩⟩
    change α = algebraMap ℤ (𝓞 K) x - -r q
    change (algebraMap ℤ (𝓞 K) x) = α - r q at hx'
    rw [hx']
    abel
  calc
    S.ncard = sf.card := Set.ncard_eq_toFinset_card _ _
    _ ≤ (Finset.univ.biUnion tf).card := Finset.card_le_card hcover
    _ ≤ ∑ q : Q, (tf q).card := Finset.card_biUnion_le
    _ = ∑ q : Q, (squareNormTranslateFiber K (β q) B).ncard := by
      apply Finset.sum_congr rfl
      intro q _
      exact (Set.ncard_eq_toFinset_card _ _).symm
    _ ≤ _ := Finset.sum_le_sum (fun q _ ↦ squareNormTranslateFiber_count_le K (β q) (hb q))

/-- The unconditional class-group-to-norm-curves reduction, with its finite
index set explicitly defined from the constructed bounded square generators. -/
theorem classGroupTwoTorsionCard_le_actual_norm_curve_family :
    let B := 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      Function.Injective β ∧
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      classGroupTwoTorsionCard K ≤
        ∑ q : boundedSquareNormTranslationClasses K B,
          (count (signedNormCurveLocus K (β q) 1)
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
          count (signedNormCurveLocus K (β q) (-1))
            (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K)))) := by
  dsimp only
  obtain ⟨β, hi, hb, hc⟩ := exists_actual_norm_curve_family K
    (9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)))
  exact ⟨β, hi, hb, (classGroupTwoTorsionCard_le_boundedSquareNormIntegers K).trans hc⟩

end
end AffineCurveCounting
