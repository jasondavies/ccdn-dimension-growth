/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.CongruenceCutoff
public import CCDN.Determinant.SmoothAffineResidueClasses
/-! A coherent choice of proper auxiliaries for every finite
smooth residue family. The structure stores conclusions of the determinant
theorem; its existence is proved from the equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

def SmoothAffineResidueFamily.restrict {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

def emptySmoothAffineResidueFamily {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

structure SurfaceCongruenceFamily (f : MvPolynomial (Fin 3) ℤ) (B A : ℝ) where
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → MvPolynomial (Fin 3) ℤ
  nonzero : ∀ P hP r, auxiliary P hP r ≠ 0
  proper : ∀ P hP r, ¬ map (Int.castRingHom ℚ) f ∣
    map (Int.castRingHom ℚ) (auxiliary P hP r)
  degree_le : ∀ P hP r, ((auxiliary P hP r).totalDegree : ℝ) ≤
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) + 1) * (1 + Real.log B + ∑ p ∈ P, Real.log p)
  vanishes : ∀ P hP r x, x ∈ affineCongruencePoints f B P (smoothResidueIntegerLift r) →
    eval x (auxiliary P hP r) = 0

theorem exists_surface_congruence_family
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    Nonempty (SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K)) := by
  classical
  have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :=
    exists_surface_congruence_auxiliary f hir hd hK hH hB hcoeff hheight P hP
      (smoothResidueIntegerLift r)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_zero r p hp)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_smooth r p hp)
  choose g hg0 hgproper hgdegree hgzero using hex
  exact ⟨⟨g, hg0, hgproper, hgdegree, hgzero⟩⟩

def SurfaceCongruenceFamily.initial {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

lemma SurfaceCongruenceFamily.initial_eq {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f := by
    funext p
    exact False.elim (notMem_empty p.val p.property)
  rw [he]
  rfl

lemma SurfaceCongruenceFamily.initial_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0) :
    eval x F.initial = 0 :=
  F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x
    (mem_affineCongruencePoints.mpr ⟨hx, hxf, by simp⟩)

lemma SurfaceCongruenceFamily.point_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    eval x (F.auxiliary P hP (smoothResidueFamilyOfPoint x hxf P hs)) = 0 := by
  apply F.vanishes
  apply mem_affineCongruencePoints.mpr
  refine ⟨hx, hxf, ?_⟩
  intro p hp j
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact smoothResidueFamilyOfPoint_congruence x hxf P hs p hp j

end
end CCDN
