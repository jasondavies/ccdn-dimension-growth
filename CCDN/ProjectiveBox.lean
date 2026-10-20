module

public import CCDN.Box
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

/-! Rational projective points with the multiplicative height used by CCDN.
Bounded-height sets are finite, and primitive integral coordinates recover
the paper's maximum-coordinate height. No counting estimate is assumed. -/

@[expose] public section
namespace CCDN
noncomputable section

abbrev ProjectivePoint (n : ℕ) := Projectivization ℚ (Fin (n + 1) → ℚ)

lemma projective_rep_height {n : ℕ} (x : ProjectivePoint n) :
    Height.mulHeight x.rep = x.mulHeight := by
  rw [← Projectivization.mulHeight_mk x.rep_nonzero, x.mk_rep]

/-- Every coordinate ratio has height bounded by the projective height. -/
lemma projective_coordinate_ratio_height {n : ℕ} (x : ProjectivePoint n)
    (i j : Fin (n + 1)) :
    Height.mulHeight₁ (x.rep j / x.rep i) ≤ x.mulHeight := by
  rw [Height.mulHeight₁_div_eq_mulHeight]
  have h := Height.mulHeight_comp_le (![j, i] : Fin 2 → Fin (n + 1)) x.rep
  have he : x.rep ∘ ![j, i] = ![x.rep j, x.rep i] := by
    funext k
    fin_cases k <;> rfl
  rw [he, projective_rep_height] at h
  exact h

/-- Northcott finiteness in rational projective space, proved using affine charts. -/
theorem projective_height_finite (n : ℕ) (B : ℝ) :
    {x : ProjectivePoint n | x.mulHeight ≤ B}.Finite := by
  classical
  have hv : {v : Fin (n + 1) → ℚ | ∀ j, Height.mulHeight₁ (v j) ≤ B}.Finite := by
    exact Set.Finite.pi' fun _ => Northcott.finite_le B
  have hs : {v : {v : Fin (n + 1) → ℚ // v ≠ 0} |
      ∀ j, Height.mulHeight₁ (v.val j) ≤ B}.Finite :=
    hv.preimage Subtype.val_injective.injOn
  apply (hs.image (Projectivization.mk' ℚ)).subset
  intro x hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  change x.rep i ≠ 0 at hi
  let v : Fin (n + 1) → ℚ := fun j => x.rep j / x.rep i
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [v, hi] at this
  refine ⟨⟨v, hv0⟩, fun j => (projective_coordinate_ratio_height x i j).trans hx, ?_⟩
  rw [Projectivization.mk'_eq_mk, ← x.mk_rep, Projectivization.mk_eq_mk_iff']
  refine ⟨(x.rep i)⁻¹, ?_⟩
  funext j
  simp [v, div_eq_mul_inv, mul_comm]

/-- Actual projective points, counted once per rational line. -/
def projectivePoints {n : ℕ} (X : Set (ProjectivePoint n)) (B : ℝ) :
    Finset (ProjectivePoint n) := by
  classical
  exact (projective_height_finite n B).toFinset.filter fun x => x ∈ X

def projectiveCount {n : ℕ} (X : Set (ProjectivePoint n)) (B : ℝ) : ℕ :=
  (projectivePoints X B).card

lemma mem_projectivePoints {n : ℕ} {X : Set (ProjectivePoint n)} {B : ℝ}
    {x : ProjectivePoint n} :
    x ∈ projectivePoints X B ↔ x.mulHeight ≤ B ∧ x ∈ X := by
  classical
  simp [projectivePoints]

theorem projectiveCount_mono {n : ℕ} {X Y : Set (ProjectivePoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : projectiveCount X B ≤ projectiveCount Y C := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hB, hX⟩ := mem_projectivePoints.mp hx
  exact mem_projectivePoints.mpr ⟨hB.trans hBC, hXY hX⟩

theorem projectiveCount_union_le {n : ℕ} (X Y : Set (ProjectivePoint n)) (B : ℝ) :
    projectiveCount (X ∪ Y) B ≤ projectiveCount X B + projectiveCount Y B := by
  classical
  have h : projectivePoints (X ∪ Y) B = projectivePoints X B ∪ projectivePoints Y B := by
    ext x
    simp only [mem_projectivePoints, Finset.mem_union, Set.mem_union]
    tauto
  unfold projectiveCount
  rw [h]
  exact Finset.card_union_le _ _

lemma rationalPoint_ne_zero {n : ℕ} {x : IntPoint n} (hx : x ≠ 0) :
    rationalPoint x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  change (x i : ℚ) = 0 at hi
  exact_mod_cast hi

/-- The chosen projective height is exactly CCDN's height on primitive coordinates. -/
theorem projective_height_primitive {n : ℕ} (x : IntPoint (n + 1)) (hx : x ≠ 0)
    (hprimitive : Finset.univ.gcd x = 1) :
    (Projectivization.mk ℚ (rationalPoint x) (rationalPoint_ne_zero hx)).mulHeight =
      ((⨆ i, |x i| : ℤ) : ℝ) := by
  rw [Projectivization.mulHeight_mk]
  exact Rat.mulHeight_eq_max_abs_of_gcd_eq_one hprimitive

end
end CCDN
