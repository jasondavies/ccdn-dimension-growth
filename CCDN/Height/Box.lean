/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Integral points in real-radius boxes

Coordinates are integers; membership in the locus is tested after casting to rational numbers.
The definition works for real radii, including the boundary `B = 1` in CCDN Theorem 3.
`InBox x B` states that every coordinate of `x` has absolute value at most `B`; for points of
`ℤⁿ` it is membership in the finite box `integerBox n B` (`mem_integerBox`). The counted sets
are typically zero loci `zeroLocus f` of rational polynomials.
-/

@[expose] public section

namespace CCDN

abbrev IntPoint (n : ℕ) := Fin n → ℤ
abbrev RatPoint (n : ℕ) := Fin n → ℚ

def rationalPoint {n : ℕ} (x : IntPoint n) : RatPoint n := fun i => x i

/-- Every coordinate of the integer vector `x` has absolute value at most `B`. -/
abbrev InBox {ι : Type*} (x : ι → ℤ) (B : ℝ) : Prop :=
  ∀ i, |(x i : ℝ)| ≤ B

noncomputable def integerBox (n : ℕ) (B : ℝ) : Finset (IntPoint n) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌊B⌋) ⌊B⌋

theorem mem_integerBox {n : ℕ} {B : ℝ} {x : IntPoint n} :
    x ∈ integerBox n B ↔ InBox x B := by
  simp only [integerBox, Fintype.mem_piFinset, Finset.mem_Icc]
  apply forall_congr'
  intro i
  rw [abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hneg : -(x i) ≤ ⌊B⌋ := by omega
    have hn := Int.le_floor.mp hneg
    have hp := Int.le_floor.mp hhi
    push_cast at hn
    exact ⟨by linarith, hp⟩
  · rintro ⟨hlo, hhi⟩
    have hn : (-(x i) : ℝ) ≤ B := by linarith
    have hneg : -(x i) ≤ ⌊B⌋ := Int.le_floor.mpr (by simpa using hn)
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

noncomputable def integralPoints {n : ℕ} (X : Set (RatPoint n)) (B : ℝ) :
    Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter fun x => rationalPoint x ∈ X

noncomputable def count {n : ℕ} (X : Set (RatPoint n)) (B : ℝ) : ℕ :=
  (integralPoints X B).card

theorem mem_integralPoints {n : ℕ} {X : Set (RatPoint n)} {B : ℝ} {x : IntPoint n} :
    x ∈ integralPoints X B ↔ InBox x B ∧ rationalPoint x ∈ X := by
  classical
  simp [integralPoints, mem_integerBox]

theorem count_mono {n : ℕ} {X Y : Set (RatPoint n)} {B C : ℝ}
    (hXY : X ⊆ Y) (hBC : B ≤ C) : count X B ≤ count Y C := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hb, hx⟩ := mem_integralPoints.mp hx
  exact mem_integralPoints.mpr ⟨fun i => (hb i).trans hBC, hXY hx⟩

theorem count_union_le {n : ℕ} (X Y : Set (RatPoint n)) (B : ℝ) :
    count (X ∪ Y) B ≤ count X B + count Y B := by
  classical
  have h : integralPoints (X ∪ Y) B = integralPoints X B ∪ integralPoints Y B := by
    ext x
    simp only [mem_integralPoints, Finset.mem_union, Set.mem_union]
    tauto
  unfold count
  rw [h]
  exact Finset.card_union_le _ _

/-- The rational zeros of a polynomial with rational coefficients. -/
def zeroLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}

end CCDN
